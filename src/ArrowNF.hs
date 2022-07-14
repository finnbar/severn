{-# LANGUAGE RankNTypes #-}

module ArrowNF (module NF, module ArrowNF) where

import Helpers
import NF

import Prelude hiding (id, (.))
import Control.Arrow
import Control.Category

instance Category ANF where
    id = WithoutLoop $ lift_ Id
    g . f = composeANF g f

composeANF :: ANF b c -> ANF a b -> ANF a c
composeANF (Loop g) (Loop f) =
    Loop $
        arr_ cossa `comp`
        (f `par` id_) `comp`
        arr_ juggle `comp`
        (g `par` id_) `comp`
        arr_ juggle `comp`
        arr_ assoc
composeANF (Loop g) (WithoutLoop f) =
    Loop $ (f `par` id_) `comp` g
composeANF (WithoutLoop g) (Loop f) =
    Loop $ f `comp` (g `par` id_)
composeANF (WithoutLoop g) (WithoutLoop f) = WithoutLoop $ f `comp` g

comp :: NoLoop a b -> NoLoop b c -> NoLoop a c
comp = throughComps removeId

throughComps :: (forall a b c. NoComp a b -> NoComp b c -> Maybe (NoLoop a c)) -> NoLoop d e -> NoLoop e f -> NoLoop d f
throughComps red (WithoutComp f) (WithoutComp g) = case red f g of
    Nothing -> WithoutComp f :>>>: g
    Just nc -> nc
throughComps red (f :>>>: g) (WithoutComp h) = case red g h of
    Nothing -> throughComps red f (WithoutComp g) :>>>: h
    Just nc -> throughComps red f nc
throughComps red f (g :>>>: h) = case throughComps red g (WithoutComp h) of
    WithoutComp i -> throughComps red f (WithoutComp i)
    -- NOTE: g' = g and h' = h, but Haskell doesn't know that.
    (g' :>>>: h') -> throughComps red f g' :>>>: h'

-- SIMPLIFICATION: Id >>> f ==> f <== f >>> Id
removeId :: NoComp a b -> NoComp b c -> Maybe (NoLoop a c)
removeId f Id = Just $ WithoutComp f
removeId Id f = Just $ WithoutComp f
removeId _ _  = Nothing

-- SIMPLIFICATION: We move Id to the left as our transformation scrutinises the right.
-- NOTE: I don't think this works with nested ***, e.g. ((Id *** f) *** g) >>> ((h *** i) *** j).
squashRight :: NoComp (a,b) (c,d) -> NoComp (c,d) (e,f) -> Maybe (NoLoop (a,b) (e,f))
squashRight (f :***: g) (Id :***: h) = Just $ WithoutComp (Id :***: g) :>>>: (f :***: h)
squashRight (f :***: g) (h :***: Id) = Just $ WithoutComp (f :***: Id) :>>>: (h :***: g)
squashRight _ _ = Nothing

par :: NoLoop a b -> NoLoop a' b' -> NoLoop (a,a') (b,b')
-- SIMPLIFICATION: Id *** Id ==> Id
par (WithoutComp Id) (WithoutComp Id) = WithoutComp Id
par (WithoutComp f) (WithoutComp g) = WithoutComp $ f :***: g
par (f :>>>: g) (WithoutComp h) = (f `par` id_) `comp` (WithoutComp g `par` WithoutComp h)
par (WithoutComp f) (g :>>>: h) = (id_ `par` g) `comp` (WithoutComp f `par` WithoutComp h)
par (f :>>>: g) (h :>>>: i) = (f `par` h) `comp` (WithoutComp g `par` WithoutComp i)

instance Arrow ANF where
    arr = WithoutLoop . arr_

    WithoutLoop f *** WithoutLoop g = WithoutLoop $ f `par` g
    Loop f *** WithoutLoop g =
        Loop $
            arr_ juggle `comp`
            (f `par` g) `comp`
            arr_ juggle
    WithoutLoop f *** Loop g =
        Loop $
            arr_ assoc `comp`
            (f `par` g) `comp`
            arr_ cossa
    Loop f *** Loop g =
        Loop $
            arr_ distribute `comp`
            (f `par` g) `comp`
            arr_ distribute

instance ArrowLoop ANF where
    loop (WithoutLoop f) = Loop f
    loop (Loop f) =
        Loop $
            arr_ cossa `comp`
            f `comp`
            arr_ assoc

-- It would be lovely to enforce the product rule here, but this is challenging
-- due to Haskell not being able to easily differentiate between a type
-- variable that may contain a pair, and a pair of type variables.
-- TODO: Try to enforce this rule elsewhere.
class ArrowPre arr where
    pre :: a -> arr a a

instance ArrowPre ANF where
    pre = WithoutLoop . pre_