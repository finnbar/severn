{-# LANGUAGE Strict #-}

module Run where

import NF

runDec :: Decoupled a b -> (Val b, Val a -> Decoupled a b)
runDec (BothDec f g) =
    let (outF, fCont) = runDec f
        (outG, gCont) = runDec g
    in (Pair outF outG, \(Pair x y) -> BothDec (fCont x) (gCont y))
runDec (LoopM f d g) =
    let (outD, dCont) = runDec d
        (Pair loopOut looped, g') = runANF g outD
    in (loopOut, \v ->
            let (outF, f') = runANF f (Pair v looped)
                d' = dCont outF
            in LoopM f' d' g'
        )
runDec (Pre v) = (v, Pre)

runNoComp :: NoComp a b -> Val a -> (Val b, NoComp a b)
runNoComp (LoopD anf dec) a =
    let (outD, dCont) = runDec dec
        (Pair outl outr, anf') = runANF anf (Pair a outD)
        dec' = dCont outr
    in (outl, LoopD anf' dec')
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

runANF :: (ValidDesc a, ValidDesc b) => ANF a b -> Val a -> (Val b, ANF a b)
runANF (f :>>>: g) a =
    let (b, f') = runANF f a
        (c, g') = runANF g b
    in (c, f' :>>>: g')
runANF (Single f) a =
    let (b, f') = runNoComp f a
    in (b, Single f')