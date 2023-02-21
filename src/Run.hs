{-# LANGUAGE Strict #-}

module Run where

import ArrowCF

-- This allows CFs to be run (strictly), which we use for testing and benchmarking.

runDec :: Decoupled a b -> (Val b, Val a -> Decoupled a b)
runDec (BothDec f g) =
    let (outF, fCont) = runDec f
        (outG, gCont) = runDec g
    in (Pair outF outG, \(Pair x y) -> BothDec (fCont x) (gCont y))
runDec (LoopM f d g) =
    let (outD, dCont) = runDec d
        (Pair loopOut looped, g') = runCF g outD
    in (loopOut, \v ->
            let (outF, f') = runCF f (Pair v looped)
                d' = dCont outF
            in LoopM f' d' g'
        )
runDec (Pre v) = (v, Pre)

runNoComp :: NoComp a b -> Val a -> (Val b, NoComp a b)
runNoComp (LoopD cf dec) a =
    let (outD, dCont) = runDec dec
        (Pair outl outr, cf') = runCF cf (Pair a outD)
        dec' = dCont outr
    in (outl, LoopD cf' dec')
runNoComp (Loop _) a = undefined
runNoComp (f :***: g) (Pair a b) =
    let (l, f') = runNoComp f a
        (r, g') = runNoComp g b
    in (Pair l r, f' :***: g')
runNoComp (Arr f) a = (f a, Arr f)
runNoComp Id a = (a, Id)
runNoComp (Dec d) a =
    let (b, dCont) = runDec d
        d' = dCont a
    in (b, Dec d')

runCF :: (ValidDesc a, ValidDesc b) => CF a b -> Val a -> (Val b, CF a b)
runCF (f :>>>: g) a =
    let (b, f') = runCF f a
        (c, g') = runCF g b
    in (c, f' :>>>: g')
runCF (Single f) a =
    let (b, f') = runNoComp f a
    in (b, Single f')