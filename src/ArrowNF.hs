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

arrNoLoop :: (a -> b) -> NoLoop a b
arrNoLoop = WithoutComp . Arr

idNoLoop :: NoLoop a a
idNoLoop = WithoutComp Id

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
        arrNoLoop cossa `comp`
        (f `par` arrNoLoop id) `comp`
        arrNoLoop juggle `comp`
        (g `par` arrNoLoop id) `comp`
        arrNoLoop juggle `comp`
        arrNoLoop assoc
composeANF (Loop g) (WithoutLoop f) =
    Loop $ (f `par` arrNoLoop id) `comp` g
composeANF (WithoutLoop g) (Loop f) =
    Loop $ f `comp` (g `par` arrNoLoop id)
composeANF (WithoutLoop g) (WithoutLoop f) = WithoutLoop $ f `comp` g

comp :: NoLoop a b -> NoLoop b c -> NoLoop a c
comp (WithoutComp f) (WithoutComp g) = WithoutComp f :>>>: g
comp (f :>>>: g) (WithoutComp h) = f :>>>: g :>>>: h
comp (WithoutComp f) (g :>>>: h) = comp (WithoutComp f) g :>>>: h
comp fg (h :>>>: i) = comp fg h :>>>: i

par :: NoLoop a b -> NoLoop a' b' -> NoLoop (a,a') (b,b')
par (WithoutComp f) (WithoutComp g) = WithoutComp $ f :***: g
par (f :>>>: g) (WithoutComp h) = (f `par` idNoLoop) :>>>: (g :***: h)
par f (g :>>>: h) = (f `par` g) :>>>: (Id :***: h)

instance Arrow ANF where
    arr = WithoutLoop . arrNoLoop

    WithoutLoop f *** WithoutLoop g = WithoutLoop $ f `par` g
    Loop f *** WithoutLoop g =
        Loop $
            arrNoLoop juggle `comp`
            (f `par` g) `comp`
            arrNoLoop juggle
    WithoutLoop f *** Loop g =
        Loop $
            arrNoLoop assoc `comp`
            (f `par` g) `comp`
            arrNoLoop cossa
    Loop f *** Loop g =
        Loop $
            arrNoLoop distribute `comp`
            (f `par` g) `comp`
            arrNoLoop distribute

instance ArrowLoop ANF where
    loop (WithoutLoop f) = Loop f
    loop (Loop f) =
        Loop $
            arrNoLoop cossa `comp`
            f `comp`
            arrNoLoop assoc

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