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

throughComps :: (forall a b c. NoComp a b -> NoComp b c -> NoLoop a c) -> NoLoop d e -> NoLoop e f -> NoLoop d f
throughComps red (WithoutComp f) (WithoutComp g) = red f g
throughComps red (f :>>>: g) (WithoutComp h) = throughComps red f (red g h)
throughComps red f (g :>>>: h) = case throughComps red g (WithoutComp h) of
    WithoutComp i -> throughComps red f (WithoutComp i)
    -- NOTE: g' = g and h' = h, but Haskell doesn't know that.
    (g' :>>>: h') -> throughComps red f g' :>>>: h'

-- SIMPLIFICATION: Id >>> f ==> f <== f >>> Id
removeId :: NoComp a b -> NoComp b c -> NoLoop a c
removeId f Id = WithoutComp f
removeId Id f = WithoutComp f
removeId f g  = WithoutComp f :>>>: g

-- SIMPLIFICATION: We move Id to the left as our transformation scrutinises the right.
squashRight :: NoComp a b -> NoComp b c -> NoLoop a c
squashRight f Id = WithoutComp Id :>>>: f
squashRight (f :***: g) (h :***: i) =
    squashRight f h `par` squashRight g i
-- SIMPLIFICATION: Pre is separated via product rule.
squashRight (f :***: g) (Pre (i,j)) =
    squashRight (f :***: g) (Pre i :***: Pre j)
squashRight f g = WithoutComp f :>>>: g

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
class ArrowPre arr where
    pre :: a -> arr a a

instance ArrowPre ANF where
    pre = WithoutLoop . pre_