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
        (Pair loopOut looped, g') = runALP g outD
    in (loopOut, \v ->
            let (outF, f') = runALP f (Pair v looped)
                d' = dCont outF
            in LoopM f' d' g'
        )
runDec (Pre' v) = (v, Pre')

runNoComp' :: NoComp' a b -> Val a -> (Val b, NoComp' a b)
runNoComp' (LoopD alp dec) a = undefined
runNoComp' (f :****: g) (Pair a b) =
    let (l, f') = runNoComp' f a
        (r, g') = runNoComp' g b
    in (Pair l r, f' :****: g')
runNoComp' (Arr' f) a = (f a, Arr' f)
runNoComp' Id' a = (a, Id')
runNoComp' (Dec d) a =
    let (b, dCont) = runDec d
        d' = dCont a
    in (b, Dec d')

runALP :: (ValidDesc a, ValidDesc b) => ALP a b -> Val a -> (Val b, ALP a b)
runALP (f :>>>>: g) a =
    let (b, f') = runALP f a
        (c, g') = runALP g b
    in (c, f' :>>>>: g')
runALP (Sing f) a =
    let (b, f') = runNoComp' f a
    in (b, Sing f')