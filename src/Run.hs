{-# LANGUAGE Strict #-}

module Run where

import NF

runNoLoop :: NoLoop a b -> Val a -> (Val b, NoLoop a b)
runNoLoop (f :>>>: g) a =
    let (intermediate, f') = runNoLoop f a
        (final, g') = runNoComp g intermediate
    in (final, f' :>>>: g')
runNoLoop (WithoutComp f) a = let (b, cont) = runNoComp f a in (b, WithoutComp cont)

runNoComp :: NoComp a b -> Val a -> (Val b, NoComp a b)
runNoComp (f :***: g) (Pair a b) =
    let (l, f') = runNoComp f a
        (r, g') = runNoComp g b
    in (Pair l r, f' :***: g')
runNoComp (Arr f) a = (f a, Arr f)
runNoComp (Pre i) a = (i, Pre a)
runNoComp Id a = (a, Id)
runNoComp Assoc (Pair (Pair a b) c) = (Pair a (Pair b c), Assoc)
runNoComp Cossa (Pair a (Pair b c)) = (Pair (Pair a b) c, Cossa)
runNoComp Juggle (Pair (Pair a b) c) = (Pair (Pair a c) b, Juggle)
runNoComp Distribute (Pair (Pair a b) (Pair c d)) =
    (Pair (Pair a c) (Pair b d), Distribute)
runNoComp Squish (Pair a (Pair b c)) = (Pair b (Pair a c), Squish)

runALP :: (ValidDesc a, ValidDesc b) => ALP a b -> Val a -> (Val b, ALP a b)
runALP (WithoutLoopPre f) a =
    let (b, f') = runNoLoop f a
    in (b, WithoutLoopPre f')
runALP (LoopPre i f) a =
    let (Pair b c, f') = runNoLoop f (Pair a i)
    in (b, LoopPre c f')
