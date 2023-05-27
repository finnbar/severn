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

prog11 :: Quote m => Int -> (Code m (SF Double Double), Code m (CFSF (V Double) (V Double)))
prog11 1 = ([|| in1out1sf ||], [|| Single in1out1nc ||])
prog11 2 = ([|| in1out2sf A.>>> in2out1sf ||], [|| Single in1out2nc :>>>: Single in2out1nc ||])
prog11 n =
    let (sfprog, cfsfprog) = prog22 (n-2)
    in ([|| in1out2sf A.>>> $$sfprog A.>>> in2out1sf ||], [|| Single in1out2nc :>>>: $$cfsfprog :>>>: Single in2out1nc ||])

make :: Quote m => (Code m a, Code m b) -> Code m (a, b)
make (l, r) = [|| ($$l, $$r) ||]

prog22 :: Quote m => Int -> (Code m (SF (Double, Double) (Double, Double)), Code m (CFSF (P (V Double) (V Double)) (P (V Double) (V Double))))
prog22 1 = ([|| in2out2sf ||], [|| Single in2out2nc ||])
prog22 2 = ([|| in2out2sf A.>>> (in1out1sf A.*** in1out1sf) ||], [|| Single in2out2nc :>>>: Single (in1out1nc :***: in1out1nc) ||])
prog22 n =
    let (sfl, cfsfl) = prog22 2
        (sfr, cfsfr) = prog22 (n-2)
    in ([|| $$sfl A.>>> $$sfr ||], [|| $$cfsfl :>>>: $$cfsfr ||])

-- loop ((id *** f) >>> (id *** pre) >>> g)
loopD :: Quote m => Int -> (Code m (SF Double Double), Code m (CFSF (V Double) (V Double)))
loopD n =
    let (n1, n2) = bisect n
        (sff, cfsff) = prog11 n1
        (sfg, cfsfg) = prog22 n2
    in ([|| A.loop ((C.id A.*** ($$sff A.>>> iPre 0)) A.>>> $$sfg) ||],
        [|| Single $ Loop ((Single Id *** ($$cfsff >>> Single (Dec (Pre (One 0))))) >>> $$cfsfg) ||])

-- loop (f >>> pre >>> g)
loopM :: Quote m => Int -> (Code m (SF Double Double), Code m (CFSF (V Double) (V Double)))
loopM n =
    let (n1, n2) = bisect n
        (sff, cfsff) = prog22 n1
        (sfg, cfsfg) = prog22 n2
    in ([|| A.loop ($$sff A.>>> iPre (0,0) A.>>> $$sfg) ||],
        [|| Single $ Loop ($$cfsff :>>>: pre (Pair (One 0) (One 0)) :>>>: $$cfsfg) ||])

-- loop ((id *** f) >>> (id *** loop (h >>> pre >>> i)) >>> g)
loopDloopM :: Quote m => Int -> (Code m (SF Double Double), Code m (CFSF (V Double) (V Double)))
loopDloopM n =
    let (fgn, loopn) = bisect n
        (sfinner, cfsfinner) = loopM loopn
        (fn, gn) = bisect fgn
        (sff, cfsff) = prog11 fn
        (sfg, cfsfg) = prog22 gn
    in ([|| A.loop ((C.id A.*** ($$sff A.>>> $$sfinner)) A.>>> $$sfg) ||],
        [|| Single $ Loop ((Single Id *** ($$cfsff >>> $$cfsfinner)) >>> $$cfsfg) ||])