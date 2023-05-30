{-# LANGUAGE TemplateHaskell, DataKinds, BangPatterns #-}

module ProgGenTH where

import ArbitraryProgram (PDesc(..))
import TestHelpers (Simplify)
import BenchHelpers (bisect)
import FRP.Yampa (SF, iPre)
import qualified Control.Arrow as A
import qualified Control.Category as C (id)
import CFSF
import ArrowCFSF

import Language.Haskell.TH

in1out1sf :: SF Double Double
in1out1sf = A.arr negate
in1out1nc :: NoComp (V Double) (V Double)
in1out1nc = Arr $ \(One !x) -> One (negate x)

in2out2sf :: SF (Double, Double) (Double, Double)
in2out2sf = A.arr $ \(x,y) -> let xy = x + y in (xy, negate xy)
in2out2nc :: NoComp (P (V Double) (V Double)) (P (V Double) (V Double))
in2out2nc = Arr $ \(Pair (One !x) (One !y)) -> let xy = x + y in Pair (One xy) (One $ negate xy)

in1out2sf :: SF Double (Double, Double)
in1out2sf = A.arr $ \x -> (x, x)
in1out2nc :: NoComp (V Double) (P (V Double) (V Double))
in1out2nc = Arr $ \(!x) -> Pair x x

in2out1sf :: SF (Double, Double) Double
in2out1sf = A.arr $ \(x, y) -> (x + y)
in2out1nc :: NoComp (P (V Double) (V Double)) (V Double)
in2out1nc = Arr $ \(Pair (One !x) (One !y)) -> One (x + y)

prog11 :: Quote m => Int -> (Code m (CFSF (V Double) (V Double)), Code m (SF Double Double))
prog11 1 = ([|| Single in1out1nc ||], [|| in1out1sf ||])
prog11 2 = ([|| Single in1out2nc :>>>: Single in2out1nc ||], [|| in1out2sf A.>>> in2out1sf ||])
prog11 n =
    let (cfsfprog, sfprog) = prog22 (n-2)
    in ([|| Single in1out2nc :>>>: $$cfsfprog :>>>: Single in2out1nc ||], [|| in1out2sf A.>>> $$sfprog A.>>> in2out1sf ||])

make :: Quote m => (Code m a, Code m b) -> Code m (a, b)
make (l, r) = [|| ($$l, $$r) ||]

prog22 :: Quote m => Int ->
    (Code m (CFSF (P (V Double) (V Double)) (P (V Double) (V Double))), Code m (SF (Double, Double) (Double, Double)))
prog22 1 = ([|| Single in2out2nc ||], [|| in2out2sf ||])
prog22 2 = ([|| Single in2out2nc :>>>: Single (in1out1nc :***: in1out1nc) ||], [|| in2out2sf A.>>> (in1out1sf A.*** in1out1sf) ||])
prog22 n =
    let (cfsfl, sfl) = prog22 2
        (cfsfr, sfr) = prog22 (n-2)
    in ([|| $$cfsfl :>>>: $$cfsfr ||], [|| $$sfl A.>>> $$sfr ||])

-- loop ((id *** f) >>> (id *** pre) >>> g)
loopD :: Quote m => Int -> (Code m (CFSF (V Double) (V Double)), Code m (SF Double Double))
loopD n =
    let (n1, n2) = bisect n
        (cfsff, sff) = prog11 n1
        (cfsfg, sfg) = prog22 n2
    in ([|| Single $ Loop ((Single Id *** ($$cfsff >>> Single (Dec (Pre (One 0))))) >>> $$cfsfg) ||],
        [|| A.loop ((C.id A.*** ($$sff A.>>> iPre 0)) A.>>> $$sfg) ||])

-- loop (f >>> pre >>> g)
loopM :: Quote m => Int -> (Code m (CFSF (V Double) (V Double)), Code m (SF Double Double))
loopM n =
    let (n1, n2) = bisect n
        (cfsff, sff) = prog22 n1
        (cfsfg, sfg) = prog22 n2
    in ([|| Single $ Loop ($$cfsff :>>>: pre (Pair (One 0) (One 0)) :>>>: $$cfsfg) ||],
        [|| A.loop ($$sff A.>>> iPre (0,0) A.>>> $$sfg) ||])

-- loop ((id *** f) >>> (id *** loop (h >>> pre >>> i)) >>> g)
loopDloopM :: Quote m => Int -> (Code m (CFSF (V Double) (V Double)), Code m (SF Double Double))
loopDloopM n =
    let (fgn, loopn) = bisect n
        (cfsfinner, sfinner) = loopM loopn
        (fn, gn) = bisect fgn
        (cfsff, sff) = prog11 fn
        (cfsfg, sfg) = prog22 gn
    in ([|| Single $ Loop ((Single Id *** ($$cfsff >>> $$cfsfinner)) >>> $$cfsfg) ||],
        [|| A.loop ((C.id A.*** ($$sff A.>>> $$sfinner)) A.>>> $$sfg) ||])

-- pre v1 >>> arr f1 >>> pre v2 >>> arr f2 >>> ... >>> pre vn >>> arr fn
preChain :: Quote m => Int ->
    (Code m (CFSF (P (V Double) (V Double)) (P (V Double) (V Double))),
    Code m (SF (Double, Double) (Double, Double)))
preChain 0 = ([|| Single (Id :***: Id) ||], [|| C.id ||])
preChain 1 = ([|| Single $ Dec (Pre (One 0)) :***: Dec (Pre (One 0)) ||],
    [|| iPre (0,0) ||])
preChain 2 =
    let (cfsfl, sfl) = preChain 1
    in ([|| $$cfsfl :>>>: Single in2out2nc ||], [|| $$sfl A.>>> in2out2sf ||])
preChain n =
    let (cfsfr, sfr) = preChain (n-2)
        (cfsfl, sfl) = preChain 2
    in ([|| $$cfsfl :>>>: $$cfsfr ||], [|| $$sfl A.>>> $$sfr ||])

-- loop preChain
manyPreLoop :: Quote m => Int ->
    (Code m (CFSF (V Double) (V Double)), Code m (SF Double Double))
manyPreLoop n =
    let (cfsf, sf) = preChain n
    in ([|| Single $ Loop $$cfsf ||], [|| A.loop $$sf ||])