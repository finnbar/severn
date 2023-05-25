{-# LANGUAGE TemplateHaskell, DataKinds, BangPatterns #-}

module ProgGenTH where

-- TODO: Splice for arbitrary prog of size/arity
-- Then splice for single loop
-- Then test those (one loop of size x, zero loops of size x)

import ArbitraryProgram (PDesc(..))
import TestHelpers (Simplify)
import FRP.Yampa (SF)
import qualified Control.Arrow as A
import CFSF

import Language.Haskell.TH

in1out1 :: Quote m => (Code m (SF Double Double), Code m (NoComp (V Double) (V Double)))
in1out1 = ([|| A.arr negate ||],
    [|| Arr $ \(One !x) -> One (negate x) ||])

in2out2 :: Quote m => (Code m (SF (Double, Double) (Double, Double)), Code m (NoComp (P (V Double) (V Double)) (P (V Double) (V Double))))
in2out2 = ([|| A.arr $ \(x,y) -> let xy = x + y in (xy, negate xy) ||],
    [|| Arr $ \(Pair (One !x) (One !y)) -> let xy = x + y in Pair (One xy) (One $ negate xy) ||])

in1out2 :: Quote m => (Code m (SF Double (Double, Double)), Code m (NoComp (V Double) (P (V Double) (V Double))))
in1out2 = ([|| A.arr $ \x -> (x, x) ||],
    [|| Arr $ \(!x) -> Pair x x ||])

in2out1 :: Quote m => (Code m (SF (Double, Double) Double), Code m (NoComp (P (V Double) (V Double)) (V Double)))
in2out1 = ([|| A.arr $ \(x, y) -> (x + y) ||],
    [|| Arr $ \(Pair (One !x) (One !y)) -> One (x + y) ||])

prog11 :: Quote m => Int -> (Code m (SF Double Double), Code m (CFSF (V Double) (V Double)))
prog11 1 = let (sf, nocomp) = in1out1 in ([|| $$sf ||], [|| Single $$nocomp ||])
prog11 2 =
    let (sf1, nocomp1) = in1out2
        (sf2, nocomp2) = in2out1
    in ([|| $$sf1 A.>>> $$sf2 ||], [|| Single $$nocomp1 :>>>: Single $$nocomp2 ||])
prog11 n =
    let (sf1, nocomp1) = in1out2
        (sf2, nocomp2) = in2out1
        (sfprog, cfsfprog) = prog22 (n-2)
    in ([|| $$sf1 A.>>> $$sfprog A.>>> $$sf2 ||], [|| Single $$nocomp1 :>>>: $$cfsfprog :>>>: Single $$nocomp2 ||])

makeProg11 :: Quote m => Int -> Code m (SF Double Double, CFSF (V Double) (V Double))
makeProg11 n =
    let (sf, cfsf) = prog11 n
    in [|| ($$sf, $$cfsf) ||]

prog22 :: Quote m => Int -> (Code m (SF (Double, Double) (Double, Double)), Code m (CFSF (P (V Double) (V Double)) (P (V Double) (V Double))))
prog22 1 = let (sf, nocomp) = in2out2 in ([|| $$sf ||], [|| Single $$nocomp ||])
prog22 2 =
    let (sf1, nocomp1) = in2out2
        (sf2, nocomp2) = in1out1
        (sf3, nocomp3) = in1out1
    in ([|| $$sf1 A.>>> ($$sf2 A.*** $$sf3) ||], [|| Single $$nocomp1 :>>>: Single ($$nocomp2 :***: $$nocomp3) ||])
prog22 n =
    let (sfl, cfsfl) = prog22 2
        (sfr, cfsfr) = prog22 (n-2)
    in ([|| $$sfl A.>>> $$sfr ||], [|| $$cfsfl :>>>: $$cfsfr ||])