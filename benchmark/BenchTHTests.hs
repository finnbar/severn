{-# LANGUAGE TemplateHaskell, GADTs, DataKinds #-}

module BenchTHTests where

import TestPrograms
import ProgGenTH
import CFSF

import Criterion
import Criterion.Types
import Criterion.Main

benchTHTests :: IO ()
benchTHTests = do
    let ins' = [1..100000]
        ins = map One ins'
    nl <- noloop (ins, ins')
    ld <- loopD (ins, ins')
    lm <- loopM (ins, ins')
    let benches = [nl, ld, lm]
    defaultMainWith (defaultConfig {csvFile = Just "th_out.csv"}) benches

noloop :: ([Val (V Double)], [Double]) -> IO Benchmark
noloop (ins, ins') = do
    single100 <- benchmarkSet "100" $$(makeProg11 100) (ins, ins')
    single200 <- benchmarkSet "200" $$(makeProg11 200) (ins, ins')
    single300 <- benchmarkSet "300" $$(makeProg11 300) (ins, ins')
    let benches = [single100, single200, single300]
    return $ bgroup "noloop" benches

loopD :: ([Val (V Double)], [Double]) -> IO Benchmark
loopD (ins, ins') = do
    ld100 <- benchmarkSet "100" $$(makeLoopD 100) (ins, ins')
    ld200 <- benchmarkSet "200" $$(makeLoopD 200) (ins, ins')
    ld300 <- benchmarkSet "300" $$(makeLoopD 300) (ins, ins')
    let benches = [ld100, ld200, ld300]
    return $ bgroup "loopD" benches

loopM :: ([Val (V Double)], [Double]) -> IO Benchmark
loopM (ins, ins') = do
    lm100 <- benchmarkSet "100" $$(makeLoopM 100) (ins, ins')
    lm200 <- benchmarkSet "200" $$(makeLoopM 200) (ins, ins')
    lm300 <- benchmarkSet "300" $$(makeLoopM 300) (ins, ins')
    let benches = [lm100, lm200, lm300]
    return $ bgroup "loopM" benches