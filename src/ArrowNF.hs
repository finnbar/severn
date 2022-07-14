module ArrowNF where

import Helpers

import Prelude hiding (id, (.))
import Control.Arrow
import Control.Category

-- ***, >>>, pre, arr, loop
-- I want the following order: loop, >>>, ***, pre/arr
data ANF a b where
    Loop :: NoLoop (a,c) (b,c) -> ANF a b
    WithoutLoop :: NoLoop a b -> ANF a b

infixl 1 :>>>:
data NoLoop a b where
    (:>>>:) :: NoLoop a b -> NoComp b c -> NoLoop a c
    WithoutComp :: NoComp a b -> NoLoop a b

lift_ :: NoComp a b -> NoLoop a b
lift_ = WithoutComp

arr_ :: (a -> b) -> NoLoop a b
arr_ = WithoutComp . Arr

id_ :: NoLoop a a
id_ = WithoutComp Id

infixl 3 :***:
data NoComp a b where
    (:***:) :: NoComp a b -> NoComp a' b' -> NoComp (a,a') (b,b')
    Arr :: (a -> b) -> NoComp a b
    Pre :: a -> NoComp a a
    Id :: NoComp a a

instance Category ANF where
    id = WithoutLoop $ WithoutComp Id
    g . f = composeANF g f

composeANF :: ANF b c -> ANF a b -> ANF a c
composeANF (Loop g) (Loop f) =
    Loop $
        arr_ cossa `comp`
        (f `par` arr_ id) `comp`
        arr_ juggle `comp`
        (g `par` arr_ id) `comp`
        arr_ juggle `comp`
        arr_ assoc
composeANF (Loop g) (WithoutLoop f) =
    Loop $ (f `par` arr_ id) `comp` g
composeANF (WithoutLoop g) (Loop f) =
    Loop $ f `comp` (g `par` arr_ id)
composeANF (WithoutLoop g) (WithoutLoop f) = WithoutLoop $ f `comp` g

-- NOTE: comp and par optimise, so should be preferred over direct calls to :>>>: and :***:.
-- TODO: I don't think comp transforms:
-- a *** b >>> c *** id ===> a *** id >>> c *** b
comp :: NoLoop a b -> NoLoop b c -> NoLoop a c
-- Optimisation: remove Id
comp f (WithoutComp Id) = f
comp (WithoutComp Id) f = f
-- TODO Normalisation: move Id within pairs inwards
-- Generally I need to improve my intuition of normal form, I think.
-- Normal composition:
comp (WithoutComp f) (WithoutComp g) = WithoutComp f :>>>: g
comp (f :>>>: g) (WithoutComp h) = f :>>>: g :>>>: h
comp (WithoutComp f) (g :>>>: h) = comp (WithoutComp f) g :>>>: h
comp fg (h :>>>: i) = comp fg h :>>>: i

par :: NoLoop a b -> NoLoop a' b' -> NoLoop (a,a') (b,b')
par (WithoutComp Id) (WithoutComp Id) = WithoutComp Id
par (WithoutComp f) (WithoutComp g) = WithoutComp $ f :***: g
par (f :>>>: g) (WithoutComp h) = (f `par` id_) :>>>: (g :***: h)
par (WithoutComp f) (g :>>>: h) = (id_ `par` g) :>>>: (f :***: h)
par (f :>>>: g) (h :>>>: i) = (f `par` h) :>>>: (g :***: i)

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

class ArrowPre arr where
    pre :: a -> arr a a

instance ArrowPre ANF where
    pre = WithoutLoop . WithoutComp . Pre

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

debug :: ANF a b -> String
debug = show

runANF :: ANF a b -> a -> (b, ANF a b)
runANF (Loop f) a = let ((b, c), cont) = runNoLoop f (a, c) in (b, Loop cont)
runANF (WithoutLoop f) a = let (b, cont) = runNoLoop f a in (b, WithoutLoop cont)

runNoLoop :: NoLoop a b -> a -> (b, NoLoop a b)
runNoLoop (f :>>>: g) a =
    let (intermediate, f') = runNoLoop f a
        (final, g') = runNoComp g intermediate
    in (final, f' :>>>: g')
runNoLoop (WithoutComp f) a = let (b, cont) = runNoComp f a in (b, WithoutComp cont)

runNoComp :: NoComp a b -> a -> (b, NoComp a b)
runNoComp (f :***: g) (a, b) =
    let (l, f') = runNoComp f a
        (r, g') = runNoComp g b
    in ((l, r), f' :***: g')
runNoComp (Arr f) a = (f a, Arr f)
runNoComp (Pre i) a = (i, Pre a)
runNoComp Id a = (a, Id)