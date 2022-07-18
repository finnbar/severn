{-# LANGUAGE DataKinds, TypeFamilies, FlexibleInstances, ScopedTypeVariables #-}

module NF where

import Data.Proxy

-- * Data types and constructors

data ANF x y where
    Loop :: NoLoop (a,c) (b,c) -> ANF a b
    WithoutLoop :: NoLoop a b -> ANF a b

infixl 1 :>>>:
data NoLoop x y where
    (:>>>:) :: NoLoop a b -> NoComp b c -> NoLoop a c
    WithoutComp :: NoComp a b -> NoLoop a b

infixl 3 :***:
data NoComp x y where
    (:***:) :: NoComp a b -> NoComp a' b' -> NoComp (a,a') (b,b')
    Arr :: (a -> b) -> NoComp a b
    Pre :: a -> NoComp a a
    Id :: NoComp a a
    Squish :: NoComp (a,(b,c)) (b,(a,c))

-- * Routing instances

data ToGet = InL ToGet | InR ToGet | This

type family Get (x :: ToGet) (y :: *) where
    Get This a = a
    Get (InL tg) (a,b) = Get tg a
    Get (InR tg) (a,b) = Get tg b

class Retrieve (x :: ToGet) a b where
    retrieve :: Proxy x -> NoComp a b -> Maybe (NoComp (Get x a) (Get x b))

instance Retrieve This a b where
    retrieve _ = Just

instance Retrieve tg a c => Retrieve (InL tg) (a,b) (c,d) where
    retrieve _ (a :***: _) = retrieve (Proxy :: Proxy tg) a
    retrieve _ (Pre (i,j)) = retrieve (Proxy :: Proxy tg) (Pre i)
    retrieve _ Id = Just Id
    retrieve _ _ = Nothing

instance Retrieve tg b d => Retrieve (InR tg) (a,b) (c,d) where
    retrieve _ (_ :***: b) = retrieve (Proxy :: Proxy tg) b
    retrieve _ (Pre (i,j)) = retrieve (Proxy :: Proxy tg) (Pre j)
    retrieve _ Id = Just Id
    retrieve _ _ = Nothing

-- * Show instances

instance Show (ANF a b) where
    show (Loop f) = "Loop " ++ show f
    show (WithoutLoop f) = show f

instance Show (NoLoop a b) where
    show (f :>>>: g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (WithoutComp f) = show f

instance Show (NoComp a b) where
    show (f :***: g) = "(" ++ show f ++ " *** " ++ show g ++ ")"
    show (Arr f) = "Arr"
    show (Pre a) = "Pre"
    show Id = "Id"
    show Squish = "Squish"

-- * Running functions

debug :: ANF a b -> String
debug = show

runANF :: ANF a b -> a -> (b, ANF a b)
runANF (Loop f) a = let ((b, c), cont) = runNoLoop f (a, c) in (b, Loop cont)
runANF (WithoutLoop f) a = let (b, cont) = runNoLoop f a in (b, WithoutLoop cont)

runNoLoop :: NoLoop a b -> a -> (b, NoLoop a b)
runNoLoop (f :>>>: g) a =
    let (intermediate, f') = runNoLoop f a
        (final, g') = runNoComp g intermediate
    in (final, f' :>>>: g')
runNoLoop (WithoutComp f) a = let (b, cont) = runNoComp f a in (b, WithoutComp cont)

runNoComp :: NoComp a b -> a -> (b, NoComp a b)
runNoComp (f :***: g) (a, b) =
    let (l, f') = runNoComp f a
        (r, g') = runNoComp g b
    in ((l, r), f' :***: g')
runNoComp (Arr f) a = (f a, Arr f)
runNoComp (Pre i) a = (i, Pre a)
runNoComp Id a = (a, Id)
runNoComp Squish ~(a,~(b,c)) = ((b,(a,c)), Squish)