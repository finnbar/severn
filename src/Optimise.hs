{-# LANGUAGE DataKinds, GADTs #-}

module Optimise where

import ArrowCFSF

-- This file contains a rough optimisation using the arrow laws:
-- arr f >>> arr g = arr (g . f)
-- id >>> f = f = f >>> id
-- arr f *** arr g = arr (f *** g) for merging together arrs in parallel

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
        -- This is a little naive, but it does the job.
        (Arr f', Id) -> Arr $ firstV f'
        (Id, Arr g') -> Arr $ secondV g'
        (f', g') -> f' :***: g' 
optimiseNoComp (Loop f) = Loop $ optimiseCFSF f
optimiseNoComp (LoopD f i) = LoopD (optimiseCFSF f) i
optimiseNoComp (Dec d) = Dec $ optimiseDec d
-- Arr, Id can't be optimised.
optimiseNoComp nc = nc

optimiseCFSF :: CFSF a b -> CFSF a b
optimiseCFSF (Single nc) = Single (optimiseNoComp nc)
optimiseCFSF (f :>>>: g) = let
        f' = optimiseCFSF f
        g' = optimiseCFSF g
    in case optimiseCFSFPair f' g' of
        Just n -> optimiseCFSF n
        Nothing -> f' :>>>: g'

-- Assuming that the two input CFSFs are as optimised as possible, optimise their composition.
optimiseCFSFPair :: (ValidDesc a, ValidDesc b, ValidDesc c)
    => CFSF a b -> CFSF b c -> Maybe (CFSF a c)
-- arr f >>> arr g = arr (g.f)
optimiseCFSFPair (Single (Arr f')) (Single (Arr g')) =
    Just $ Single (Arr (g' . f'))
-- f >>> id = f = id >>> f
optimiseCFSFPair f (Single Id) = Just f
optimiseCFSFPair (Single Id) f = Just f
optimiseCFSFPair (f :>>>: g) (h :>>>: i) = optimiseCFSFPair g h >>= \v -> Just $ optimiseCFSF (f >>> v >>> i)
optimiseCFSFPair (f :>>>: g) (Single h) = optimiseCFSFPair g (Single h) >>= \v -> Just $ optimiseCFSF (f >>> v)
optimiseCFSFPair (Single f) (g :>>>: h) = optimiseCFSFPair (Single f) g >>= \v -> Just $ optimiseCFSF (v >>> h)
-- If we could optimise, this is covered by the first case
optimiseCFSFPair (Single f) (Single g) = Nothing