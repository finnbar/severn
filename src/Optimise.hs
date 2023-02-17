module Optimise where

import NF

firstV :: (ValidDesc a, ValidDesc b, ValidDesc c)
    => (Val a -> Val b) -> Val (P a c) -> Val (P b c)
firstV f (Pair x y) = Pair (f x) y

secondV :: (ValidDesc a, ValidDesc b, ValidDesc c)
    => (Val a -> Val b) -> Val (P c a) -> Val (P c b)
secondV f (Pair x y) = Pair x (f y)

bothV :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d)
    => (Val a -> Val b) -> (Val c -> Val d) ->
    Val (P a c) -> Val (P b d)
bothV f g (Pair x y) = Pair (f x) (g y)

optimiseDec :: Decoupled a b -> Decoupled a b
optimiseDec (Pre v) = Pre v
optimiseDec (LoopM f i g) = LoopM (optimiseANF f) i (optimiseANF g)
optimiseDec (BothDec f g) = BothDec (optimiseDec f) (optimiseDec g)

optimiseNoComp :: NoComp a b -> NoComp a b
optimiseNoComp (f :***: g) =
    case (optimiseNoComp f, optimiseNoComp g) of
        (Arr f', Id) -> Arr $ firstV f'
        (Id, Arr g') -> Arr $ secondV g'
        (Arr f', Arr g') -> Arr $ bothV f' g'
        (f', g') -> f' :***: g' 
optimiseNoComp (Loop f) = Loop $ optimiseANF f
optimiseNoComp (LoopD f i) = LoopD (optimiseANF f) i
optimiseNoComp (Dec d) = Dec $ optimiseDec d
-- Arr, Id can't be optimised.
optimiseNoComp nc = nc

optimiseANF :: ANF a b -> ANF a b
optimiseANF (Single nc) = Single (optimiseNoComp nc)
optimiseANF (f :>>>: g) = optimiseANFPair (optimiseANF f) (optimiseANF g)

optimiseANFPair :: (ValidDesc a, ValidDesc b, ValidDesc c)
    => ANF a b -> ANF b c -> ANF a c
optimiseANFPair (Single (Arr f')) (Single (Arr g')) =
    Single (Arr (g' . f'))
optimiseANFPair (Single (Arr f')) (Single (Arr gl :***: gr)) =
    optimiseANF $ (Single . Arr $ firstV gl . f') :>>>:
        Single (idNoComp :***: gr)
optimiseANFPair (Single (Arr f')) (Single (gl :***: Arr gr)) =
    optimiseANF $ (Single . Arr $ secondV gr . f') :>>>:
        Single (gl :***: idNoComp)
optimiseANFPair (Single (Arr fl :***: fr)) (Single (Arr g')) =
    optimiseANF $ Single (idNoComp :***: fr) :>>>:
        (Single . Arr $ g' . firstV fl)
optimiseANFPair (Single (fl :***: Arr fr)) (Single (Arr g')) =
    optimiseANF $ Single (fl :***: idNoComp) :>>>:
        (Single . Arr $ g' . secondV fr)
optimiseANFPair (Single (fl :***: Arr fr)) (Single (Arr gl :***: gr)) =
    optimiseANF $ Single (fl :***: idNoComp) :>>>:
        Single (Arr gl :***: Arr fr) :>>>:
        Single (idNoComp :***: gr)
optimiseANFPair (Single (Arr fl :***: fr)) (Single (gl :***: Arr gr)) =
    optimiseANF $ Single (idNoComp :***: fr) :>>>:
        Single (Arr fl :***: Arr gr) :>>>:
        Single (gl :***: idNoComp)
optimiseANFPair (Single (Arr fl :***: fr)) (Single (Arr gl :***: gr)) =
    optimiseANF $ Single (Arr (gl . fl) :***: fr) :>>>:
        Single (idNoComp :***: gr)
optimiseANFPair (Single (fl :***: Arr fr)) (Single (gl :***: Arr gr)) =
    optimiseANF $ Single (fl :***: Arr (gr . fr)) :>>>:
        Single (gl :***: idNoComp)
optimiseANFPair a (Single Id) = a
optimiseANFPair (Single Id) b = b
optimiseANFPair a b = a :>>>: b