module Optimise where

import ArrowCFSF

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
optimiseDec (LoopM f i g) = LoopM (optimiseCFSF f) i (optimiseCFSF g)
optimiseDec (BothDec f g) = BothDec (optimiseDec f) (optimiseDec g)

optimiseNoComp :: NoComp a b -> NoComp a b
optimiseNoComp (f :***: g) =
    case (optimiseNoComp f, optimiseNoComp g) of
        (Arr f', Arr g') -> Arr $ bothV f' g'
        (f', g') -> f' :***: g' 
optimiseNoComp (Loop f) = Loop $ optimiseCFSF f
optimiseNoComp (LoopD f i) = LoopD (optimiseCFSF f) i
optimiseNoComp (Dec d) = Dec $ optimiseDec d
-- Arr, Id can't be optimised.
optimiseNoComp nc = nc

optimiseCFSF :: CFSF a b -> CFSF a b
optimiseCFSF (Single nc) = Single (optimiseNoComp nc)
optimiseCFSF (f :>>>: g) = optimiseCFSFPair (optimiseCFSF f) (optimiseCFSF g)

optimiseCFSFPair :: (ValidDesc a, ValidDesc b, ValidDesc c)
    => CFSF a b -> CFSF b c -> CFSF a c
optimiseCFSFPair (Single (Arr f')) (Single (Arr g')) =
    Single (Arr (g' . f'))
optimiseCFSFPair (Single (Arr f')) (Single (Arr gl :***: gr)) =
    optimiseCFSF $ (Single . Arr $ firstV gl . f') :>>>:
        Single (idNoComp :***: gr)
optimiseCFSFPair (Single (Arr f')) (Single (gl :***: Arr gr)) =
    optimiseCFSF $ (Single . Arr $ secondV gr . f') :>>>:
        Single (gl :***: idNoComp)
optimiseCFSFPair (Single (Arr fl :***: fr)) (Single (Arr g')) =
    optimiseCFSF $ Single (idNoComp :***: fr) :>>>:
        (Single . Arr $ g' . firstV fl)
optimiseCFSFPair (Single (fl :***: Arr fr)) (Single (Arr g')) =
    optimiseCFSF $ Single (fl :***: idNoComp) :>>>:
        (Single . Arr $ g' . secondV fr)
optimiseCFSFPair (Single (fl :***: Arr fr)) (Single (Arr gl :***: gr)) =
    optimiseCFSF $ Single (fl :***: idNoComp) :>>>:
        Single (Arr gl :***: Arr fr) :>>>:
        Single (idNoComp :***: gr)
optimiseCFSFPair (Single (Arr fl :***: fr)) (Single (gl :***: Arr gr)) =
    optimiseCFSF $ Single (idNoComp :***: fr) :>>>:
        Single (Arr fl :***: Arr gr) :>>>:
        Single (gl :***: idNoComp)
optimiseCFSFPair (Single (Arr fl :***: fr)) (Single (Arr gl :***: gr)) =
    optimiseCFSF $ Single (Arr (gl . fl) :***: fr) :>>>:
        Single (idNoComp :***: gr)
optimiseCFSFPair (Single (fl :***: Arr fr)) (Single (gl :***: Arr gr)) =
    optimiseCFSF $ Single (fl :***: Arr (gr . fr)) :>>>:
        Single (gl :***: idNoComp)
optimiseCFSFPair a (Single Id) = a
optimiseCFSFPair (Single Id) b = b
optimiseCFSFPair a b = a :>>>: b