{-# LANGUAGE Strict, GADTs #-}

module Run where

import ArrowCFSF

-- This allows CFSFs to be run (strictly), which we use for testing and benchmarking.

-- NOTE This allocates a function at every time step.
-- This is likely part of why LoopD is slow.
-- This is also impossible to avoid without some very complex routing:
-- you need a way to get the output without the input, and then a
-- separate way of getting the continuation using the input. But for a
-- LoopM f d g, you need access to the second output of g (found while
-- getting the output) and use it when taking in the input (since that
-- is the second input of f) - which means either keeping track of
-- whether a given Decoupled has some extra data associated with it, or
-- returning a continuation like we do.
runDec :: Decoupled a b -> (Val b, Val a -> Decoupled a b)
runDec (BothDec f g) =
    let (outF, fCont) = runDec f
        (outG, gCont) = runDec g
    in (Pair outF outG, \(Pair x y) -> BothDec (fCont x) (gCont y))
runDec (LoopM f d g) =
    let (outD, dCont) = runDec d
        (Pair loopOut looped, g') = runCFSF g outD
    in (loopOut, \v ->
            let (outF, f') = runCFSF f (Pair v looped)
                d' = dCont outF
            in LoopM f' d' g'
        )
runDec (Pre v) = (v, Pre)

runDecWithInput :: Decoupled a b -> Val a -> (Val b, Decoupled a b)
runDecWithInput (BothDec f g) (Pair fi gi) =
    let (fo, f') = runDecWithInput f fi
        (go, g') = runDecWithInput g gi
    in (Pair fo go, BothDec f' g')
runDecWithInput (LoopM f d g) x =
    let (outD, dcont) = runDec d
        (Pair loopOut looped, g') = runCFSF g outD
        (fout, f') = runCFSF f (Pair x looped)
    in (loopOut, LoopM f' (dcont fout) g')
runDecWithInput (Pre v) v' = (v, Pre v')

runNoComp :: NoComp a b -> Val a -> (Val b, NoComp a b)
runNoComp (LoopD cfsf dec) a =
    let (outD, dCont) = runDec dec
        (Pair outl outr, cfsf') = runCFSF cfsf (Pair a outD)
        dec' = dCont outr
    in (outl, LoopD cfsf' dec')
runNoComp (Loop _) a = undefined
runNoComp (f :***: g) (Pair a b) =
    let (l, f') = runNoComp f a
        (r, g') = runNoComp g b
    in (Pair l r, f' :***: g')
runNoComp ar@(Arr f) a = (f a, ar)
runNoComp i@Id a = (a, i)
runNoComp (Dec d) a =
    let (b, d') = runDecWithInput d a 
    in (b, Dec d')

runCFSF :: (ValidDesc a, ValidDesc b) => CFSF a b -> Val a -> (Val b, CFSF a b)
runCFSF (f :>>>: g) a =
    let (b, f') = runCFSF f a
        (c, g') = runCFSF g b
    in (c, f' :>>>: g')
runCFSF (Single f) a =
    let (b, f') = runNoComp f a
    in (b, Single f')