{-# LANGUAGE DataKinds, BangPatterns #-}

module TestPrograms where

import ProgGenTH
import CFSF
import SFRP
import PreIO
import Transform
import Optimise (optimiseCFSF)
import TestHelpers (Simplify)
import BenchHelpers

import FRP.Yampa
import Criterion

benchmarkSet :: String ->
    (SF Double Double, CFSF (V Double) (V Double)) ->
    ([Val (V Double)], [Double]) -> IO Benchmark
benchmarkSet nam (sf, cfsf) (ins, ins') = do
    let !optcfsf = optimiseCFSF cfsf
    !preIO <- compilePreIO optcfsf
    !allIO <- compile optcfsf
    return $ bgroup nam [
            bench "allIO" $ whnfAppIO (benchCompCFSF allIO) ins,
            bench "preIO" $ whnfAppIO (benchCompCFSF preIO) ins,
            bench "sf-strict" $ whnfAppIO (benchCFSF optcfsf) ins,
            bench "sf" $ whnfAppIO (benchSF sf) ins'
        ]