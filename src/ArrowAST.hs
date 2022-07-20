{-# LANGUAGE GADTs, DataKinds, StandaloneKindSignatures,
    PolyKinds, RankNTypes #-}
module ArrowAST where

import NF (ANF, Desc(..), Val(..))
import qualified ArrowNF as NF

-- A simple ArrowAST for writing tests in, so that we can validate the normal form.

type ArrowAST :: forall (s :: *) (s' :: *). Desc s -> Desc s' -> *
data ArrowAST x y where
    Arr :: (Val a -> Val b) -> ArrowAST a b
    (:>>>:) :: ArrowAST a b -> ArrowAST b c -> ArrowAST a c
    (:***:) :: ArrowAST a b -> ArrowAST a' b' -> ArrowAST (P a a') (P b b')
    First :: ArrowAST a b -> ArrowAST (P a c) (P b c)
    Second :: ArrowAST a b -> ArrowAST (P c a) (P c b)
    Pre :: Val a -> ArrowAST a a
    Loop :: NF.Loop c => ArrowAST (P a c) (P b c) -> ArrowAST a b

instance Show (ArrowAST x y) where
    show (Arr f) = "Arr"
    show (f :>>>: g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (f :***: g) = "(" ++ show f ++ " *** " ++ show g ++ ")"
    show (First f) = "First " ++ show f
    show (Second g) = "Second " ++ show g
    show (Pre _) = "Pre"
    show (Loop f) = "Loop " ++ show f

toANF :: ArrowAST a b -> ANF a b
toANF (Arr f) = NF.arr f
toANF (f :>>>: g) = toANF f NF.>>> toANF g
toANF (f :***: g) = toANF f NF.*** toANF g
toANF (First f) = NF.first (toANF f)
toANF (Second g) = NF.second (toANF g)
toANF (Pre v) = NF.pre v
toANF (Loop f) = NF.loop $ toANF f

runArrowAST :: ArrowAST a b -> Val a -> (Val b, ArrowAST a b)
runArrowAST (Arr f) a = (f a, Arr f)
runArrowAST (f :>>>: g) a =
    let (a', f') = runArrowAST f a
        (b,  g') = runArrowAST g a'
    in (b, f' :>>>: g')
runArrowAST (f :***: g) (Pair a b) =
    let (a', f') = runArrowAST f a
        (b', g') = runArrowAST g b
    in (Pair a' b', f' :***: g')
runArrowAST (First f) (Pair a b) =
    let (a', f') = runArrowAST f a
    in (Pair a' b, First f')
runArrowAST (Second g) (Pair a b) =
    let (b', g') = runArrowAST g b
    in (Pair a b', Second g')
runArrowAST (Pre v) a = (v, Pre a)
runArrowAST (Loop f) a =
    let (b, cont) = NF.loops (runArrowAST f) a
    in (b, Loop cont)
