{-# LANGUAGE RankNTypes #-}

module ArrowNF (module NF, module ArrowNF) where

import Helpers
import NF

import Prelude hiding (id, (.))
import Control.Arrow
import Control.Category

lift_ :: NoComp a b -> NoLoop a b
lift_ = WithoutComp

arr_ :: (a -> b) -> NoLoop a b
arr_ = WithoutComp . Arr

id_ :: NoLoop a a
id_ = WithoutComp Id

pre_ :: a -> NoLoop a a
pre_ = WithoutComp . Pre

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
comp (WithoutComp f) (WithoutComp g) = compSimplify f g
comp (f :>>>: g) (WithoutComp h) = case compSimplify g h of
    WithoutComp gh -> comp f (WithoutComp gh)
    (g' :>>>: h') -> comp f g' :>>>: h'
comp (WithoutComp f) (g :>>>: h) = comp (comp (WithoutComp f) g) (WithoutComp h)
comp (f :>>>: g) (h :>>>: i) = comp f $ comp (WithoutComp g) $ comp h (WithoutComp i)

-- @CompTwo@ represents exactly two composed terms.
-- This means we do not need to use `par` in `moveIdInwards` (which causes an
-- infinite loop) - we know that we are composing exactly two things so can
-- avoid calling the full version of `par`.
data CompTwo a c where
    C2 :: NoComp a b -> NoComp b c -> CompTwo a c

compTwoCompose :: CompTwo a c -> NoLoop a c
compTwoCompose (C2 x y) = WithoutComp x :>>>: y

compTwoPar :: CompTwo a b -> CompTwo a' b' -> CompTwo (a,a') (b,b')
compTwoPar (C2 a b) (C2 a' b') = C2 (parSimplify a a') (parSimplify b b')

compSimplify :: NoComp a b -> NoComp b c -> NoLoop a c
-- SIMPLIFICATION: Id >>> f ==> f <== f >>> Id
compSimplify f Id = WithoutComp f
compSimplify Id f = WithoutComp f
compSimplify f g = compTwoCompose $ moveIdInwards f g

moveIdInwards :: NoComp a b -> NoComp b c -> CompTwo a c
-- SIMPLIFICATION: If we have Id in the right pair, but non-Id in the left,
-- move that Id left.
moveIdInwards f Id = C2 Id f
moveIdInwards (a :***: b) (c :***: d) =
    compTwoPar (moveIdInwards a c) (moveIdInwards b d)
moveIdInwards (Pre ij) (c :***: d) =
    -- Important note: this looks like an unsafe pattern match, but it is fine -
    -- since we have c :***: d on the left side, b ~ (b1, b2), so a ~ (b1, b2),
    -- so we can use a tuple match.
    let (i,j) = ij in moveIdInwards (Pre i :***: Pre j) (c :***: d)
moveIdInwards f g = C2 f g

par :: NoLoop a b -> NoLoop a' b' -> NoLoop (a,a') (b,b')
par (WithoutComp f) (WithoutComp g) = WithoutComp $ parSimplify f g
par (f :>>>: g) (WithoutComp h) = (f `par` id_) `comp` WithoutComp (parSimplify g h)
par (WithoutComp f) (g :>>>: h) = (id_ `par` g) `comp` WithoutComp (parSimplify f h)
par (f :>>>: g) (h :>>>: i) = (f `par` h) `comp` WithoutComp (parSimplify g i)

parSimplify :: NoComp a b -> NoComp a' b' -> NoComp (a,a') (b,b')
-- SIMPLIFICATION: Id *** Id ==> Id
parSimplify Id Id = Id
-- SIMPLIFICATION: Pre i *** Pre j ==> Pre (i,j)
parSimplify (Pre i) (Pre j) = Pre (i,j)
parSimplify f g = f :***: g

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