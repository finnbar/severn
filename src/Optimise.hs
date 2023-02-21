module Optimise where

import ArrowCF

-- This file contains a rough optimisation using the arrow laws:
-- arr f >>> arr g = arr (g . f) and
-- id >>> f = f = f >>> id
-- We also perform a little bit of rearranging for cases like:
-- (arr f *** g) >>> arr h
-- = (id *** g) >>> (arr f *** id) >>> arr h
-- = (id *** g) >>> arr (f *** id) >>> arr h
-- = (id *** g) >>> arr (h . (f *** id))
-- through a collection of pattern matches.

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
optimiseDec (LoopM f i g) = LoopM (optimiseCF f) i (optimiseCF g)
optimiseDec (BothDec f g) = BothDec (optimiseDec f) (optimiseDec g)

optimiseNoComp :: NoComp a b -> NoComp a b
optimiseNoComp (f :***: g) =
    case (optimiseNoComp f, optimiseNoComp g) of
        (Arr f', Id) -> Arr $ firstV f'
        (Id, Arr g') -> Arr $ secondV g'
        (Arr f', Arr g') -> Arr $ bothV f' g'
        (f', g') -> f' :***: g' 
optimiseNoComp (Loop f) = Loop $ optimiseCF f
optimiseNoComp (LoopD f i) = LoopD (optimiseCF f) i
optimiseNoComp (Dec d) = Dec $ optimiseDec d
-- Arr, Id can't be optimised.
optimiseNoComp nc = nc

optimiseCF :: CF a b -> CF a b
optimiseCF (Single nc) = Single (optimiseNoComp nc)
optimiseCF (f :>>>: g) = optimiseCFPair (optimiseCF f) (optimiseCF g)

optimiseCFPair :: (ValidDesc a, ValidDesc b, ValidDesc c)
    => CF a b -> CF b c -> CF a c
optimiseCFPair (Single (Arr f')) (Single (Arr g')) =
    Single (Arr (g' . f'))
optimiseCFPair (Single (Arr f')) (Single (Arr gl :***: gr)) =
    optimiseCF $ (Single . Arr $ firstV gl . f') :>>>:
        Single (idNoComp :***: gr)
optimiseCFPair (Single (Arr f')) (Single (gl :***: Arr gr)) =
    optimiseCF $ (Single . Arr $ secondV gr . f') :>>>:
        Single (gl :***: idNoComp)
optimiseCFPair (Single (Arr fl :***: fr)) (Single (Arr g')) =
    optimiseCF $ Single (idNoComp :***: fr) :>>>:
        (Single . Arr $ g' . firstV fl)
optimiseCFPair (Single (fl :***: Arr fr)) (Single (Arr g')) =
    optimiseCF $ Single (fl :***: idNoComp) :>>>:
        (Single . Arr $ g' . secondV fr)
optimiseCFPair (Single (fl :***: Arr fr)) (Single (Arr gl :***: gr)) =
    optimiseCF $ Single (fl :***: idNoComp) :>>>:
        Single (Arr gl :***: Arr fr) :>>>:
        Single (idNoComp :***: gr)
optimiseCFPair (Single (Arr fl :***: fr)) (Single (gl :***: Arr gr)) =
    optimiseCF $ Single (idNoComp :***: fr) :>>>:
        Single (Arr fl :***: Arr gr) :>>>:
        Single (gl :***: idNoComp)
optimiseCFPair (Single (Arr fl :***: fr)) (Single (Arr gl :***: gr)) =
    optimiseCF $ Single (Arr (gl . fl) :***: fr) :>>>:
        Single (idNoComp :***: gr)
optimiseCFPair (Single (fl :***: Arr fr)) (Single (gl :***: Arr gr)) =
    optimiseCF $ Single (fl :***: Arr (gr . fr)) :>>>:
        Single (gl :***: idNoComp)
optimiseCFPair a (Single Id) = a
optimiseCFPair (Single Id) b = b
optimiseCFPair a b = a :>>>: b