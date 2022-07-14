{-# LANGUAGE GADTs #-}

-- This is an example implementation of Arrow for us to compare ANF to.

module ArrowAST where

import Prelude hiding ((.), id)
import Control.Category
import Control.Arrow

import ArrowNF (ArrowPre(..))

data AAST a b where
    Arr :: (a -> b) -> AAST a b
    (:>>>:) :: AAST a b -> AAST b c -> AAST a c
    (:***:) :: AAST a b -> AAST a' b' -> AAST (a,a') (b,b')
    Loop :: AAST (a,c) (b,c) -> AAST a b
    (:+++:) :: AAST a b -> AAST a' b' -> AAST (Either a a') (Either b b')
    Pre :: a -> AAST a a
    Switch :: AAST a (b, Maybe c) -> (c -> AAST a b) -> AAST a b

instance Category AAST where
    id = Arr id
    g . f = f :>>>: g

instance Arrow AAST where
    arr = Arr
    f *** g = f :***: g

instance ArrowLoop AAST where
    loop = Loop

instance ArrowChoice AAST where
    f +++ g = f :+++: g

instance ArrowPre AAST where
    pre = Pre

runAAST :: AAST a b -> a -> (b, AAST a b)
runAAST (Arr f) a = (f a, Arr f)
runAAST (f :>>>: g) a =
    let (int, f') = runAAST f a
        (res, g') = runAAST g int
    in (res, f' :>>>: g')
runAAST (f :***: g) (a, b) =
    let (a', f') = runAAST f a
        (b', g') = runAAST g b
    in ((a', b'), f' :***: g')
runAAST (Loop f) a =
    let ((b,c), f') = runAAST f (a,c) in (b, Loop f')
runAAST (f :+++: g) (Left a) =
    let (b, f') = runAAST f a in (Left b, f' +++ g)
runAAST (f :+++: g) (Right a) =
    let (b, g') = runAAST g a in (Right b, f +++ g')
runAAST (Pre i) a = (i, Pre a)
runAAST (Switch st ct) a =
    let ((b, mc), st') = runAAST st a
    in case mc of
        Nothing -> (b, Switch st' ct)
        Just c -> let aast = ct c in runAAST aast a