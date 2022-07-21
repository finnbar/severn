{-# LANGUAGE StandaloneKindSignatures, DataKinds, PolyKinds, RankNTypes,
    FlexibleContexts #-}

module NF where

-- * Data types and constructors

type Desc :: * -> *
data Desc x where
    V :: a -> Desc a
    P :: Desc a -> Desc b -> Desc (a,b)

type Val :: forall s. Desc s -> *
data Val x where
    One :: a -> Val (V a)
    Pair :: Val a -> Val b -> Val (P a b)

type ANF :: forall s s'. Desc s -> Desc s' -> *
data ANF x y where
    Loop :: NoLoop (P a c) (P b c) -> ANF a b
    WithoutLoop :: NoLoop a b -> ANF a b

infixl 1 :>>>:
type NoLoop :: forall s s'. Desc s -> Desc s' -> *
data NoLoop x y where
    (:>>>:) :: NoLoop a b -> NoComp b c -> NoLoop a c
    WithoutComp :: NoComp a b -> NoLoop a b

infixl 3 :***:
type NoComp :: forall s s'. Desc s -> Desc s' -> *
data NoComp x y where
    (:***:) :: NoComp a b -> NoComp a' b' -> NoComp (P a a') (P b b')
    Arr :: (Val a -> Val b) -> NoComp a b
    Pre :: Val a -> NoComp a a
    Id :: NoComp a a
    Squish :: NoComp (P a (P b c)) (P b (P a c))
    Assoc :: NoComp (P (P a b) c) (P a (P b c))
    Cossa :: NoComp (P a (P b c)) (P (P a b) c)
    Juggle :: NoComp (P (P a b) c) (P (P a c) b)
    Distribute :: NoComp (P (P a b) (P c d)) (P (P a c) (P b d))

-- * Show instances

instance Show a => Show (Val (V a)) where
    show (One a) = show a
instance (Show (Val a), Show (Val b)) => Show (Val (P a b)) where
    show (Pair a b) = "[|" ++ show a ++ ", " ++ show b ++ "|]"

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
    show Assoc = "Assoc"
    show Cossa = "Cossa"
    show Juggle = "Juggle"
    show Distribute = "Distribute"

-- * Eq instances

instance Eq a => Eq (Val (V a)) where
    One a == One b = a == b

instance (Eq (Val a), Eq (Val b)) => Eq (Val (P a b)) where
    Pair a b == Pair a' b' = a == a' && b == b'

-- * Running functions

debug :: ANF a b -> String
debug = show

runANF :: ANF a b -> Val a -> (Val b, ANF a b)
runANF (Loop f) a = let (Pair b c, cont) = runNoLoop f (Pair a c) in (b, Loop cont)
runANF (WithoutLoop f) a = let (b, cont) = runNoLoop f a in (b, WithoutLoop cont)

runNoLoop :: NoLoop a b -> Val a -> (Val b, NoLoop a b)
runNoLoop (f :>>>: g) a =
    let (intermediate, f') = runNoLoop f a
        (final, g') = runNoComp g intermediate
    in (final, f' :>>>: g')
runNoLoop (WithoutComp f) a = let (b, cont) = runNoComp f a in (b, WithoutComp cont)

runNoComp :: NoComp a b -> Val a -> (Val b, NoComp a b)
runNoComp (f :***: g) (Pair a b) =
    let (l, f') = runNoComp f a
        (r, g') = runNoComp g b
    in (Pair l r, f' :***: g')
runNoComp (Arr f) a = (f a, Arr f)
runNoComp (Pre i) a = (i, Pre a)
runNoComp Id a = (a, Id)
runNoComp Squish (Pair a (Pair b c)) = (Pair b (Pair a c), Squish)
runNoComp Assoc (Pair (Pair a b) c) = (Pair a (Pair b c), Assoc)
runNoComp Cossa (Pair a (Pair b c)) = (Pair (Pair a b) c, Cossa)
runNoComp Juggle (Pair (Pair a b) c) = (Pair (Pair a c) b, Juggle)
runNoComp Distribute (Pair (Pair a b) (Pair c d)) =
    (Pair (Pair a c) (Pair b d), Distribute)