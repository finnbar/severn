module ArrowNF (module NF, module ArrowNF) where

import NF

import Prelude hiding (id)

composeANF :: ANF b c -> ANF a b -> ANF a c
composeANF (Loop g) (Loop f) =
    Loop $
        lift_ Cossa `comp`
        (f `par` id_) `comp`
        lift_ Juggle `comp`
        (g `par` id_) `comp`
        lift_ Juggle `comp`
        lift_ Assoc
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

compTwoCompose :: CompTwo a c -> NoLoop a c
-- SIMPLIFICATION: Id >>> f ==> f <== f >>> Id
-- This is partially covered in `compSimplify` but needs restating here as we
-- never check this condition _after_ moveIdInwards.
compTwoCompose (C2 Id y) = WithoutComp y
compTwoCompose (C2 x Id) = WithoutComp x
compTwoCompose (C2 x y) = WithoutComp x :>>>: y

compTwoPar :: CompTwo a b -> CompTwo a' b' -> CompTwo (P a a') (P b b')
compTwoPar (C2 a b) (C2 a' b') = C2 (parSimplify a a') (parSimplify b b')

compSimplify :: NoComp a b -> NoComp b c -> NoLoop a c
-- SIMPLIFICATION: Id >>> f ==> f <== f >>> Id
compSimplify f Id = WithoutComp f
compSimplify Id f = WithoutComp f
compSimplify f g = compTwoCompose $ moveIdInwards f g

-- CompTwo means we do not need to use `par` here, which would cause an
-- infinite loop - we know that we are composing exactly two things so can
-- avoid calling the full version of `par`.
moveIdInwards :: NoComp a b -> NoComp b c -> CompTwo a c
-- SIMPLIFICATION: If we have Id in the right pair, but non-Id in the left,
-- move that Id left.
moveIdInwards f Id = C2 Id f
moveIdInwards (a :***: b) (c :***: d) =
    compTwoPar (moveIdInwards a c) (moveIdInwards b d)
moveIdInwards f g = C2 f g

par :: NoLoop a b -> NoLoop a' b' -> NoLoop (P a a') (P b b')
par (WithoutComp f) (WithoutComp g) = WithoutComp $ parSimplify f g
par (f :>>>: g) (WithoutComp h) = (f `par` id_) `comp` WithoutComp (parSimplify g h)
par (WithoutComp f) (g :>>>: h) = (id_ `par` g) `comp` WithoutComp (parSimplify f h)
par (f :>>>: g) (h :>>>: i) = (f `par` h) `comp` WithoutComp (parSimplify g i)

parSimplify :: NoComp a b -> NoComp a' b' -> NoComp (P a a') (P b b')
-- SIMPLIFICATION: Id *** Id ==> Id
parSimplify Id Id = Id
parSimplify f g = f :***: g

-- THE ARROW API FOR ANF

id :: ANF a a
id = WithoutLoop $ lift_ Id

(>>>) :: ANF a b -> ANF b c -> ANF a c
f >>> g = composeANF g f

arr :: (Val a -> Val b) -> ANF a b
arr = WithoutLoop . arr_

(***) :: ANF a b -> ANF a' b' -> ANF (P a a') (P b b')
WithoutLoop f *** WithoutLoop g = WithoutLoop $ f `par` g
Loop f *** WithoutLoop g =
    Loop $
        lift_ Juggle `comp`
        (f `par` g) `comp`
        lift_ Juggle
WithoutLoop f *** Loop g =
    Loop $
        lift_ Assoc `comp`
        (f `par` g) `comp`
        lift_ Cossa
Loop f *** Loop g =
    Loop $
        lift_ Distribute  `comp`
        (f `par` g) `comp`
        lift_ Distribute

first :: ANF a b -> ANF (P a c) (P b c)
first = (*** id)
second :: ANF a b -> ANF (P c a) (P c b)
second = (id ***)

loop :: ANF (P a c) (P b c) -> ANF a b
loop (WithoutLoop f) = Loop f
loop (Loop f) =
    Loop $
        lift_ Cossa `comp`
        f `comp`
        lift_ Assoc

pre :: Val a -> ANF a a
pre = WithoutLoop . pre_