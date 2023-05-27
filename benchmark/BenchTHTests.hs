{-# LANGUAGE TemplateHaskell, GADTs, DataKinds #-}

module BenchTHTests where

import TestPrograms
import ProgGenTH
import CFSF

import Criterion
import Criterion.Types
import Criterion.Main
import Statistics.Types (cl99)

benchTHTests :: IO ()
benchTHTests = do
    nl <- noloop
    ld <- benchLoopD
    lm <- benchLoopM
    ldlm <- benchLoopDLoopM
    let benches = [ld]
    defaultMainWith (defaultConfig {csvFile = Just "th_out.csv", confInterval = cl99, timeLimit = 20}) benches

noloop :: IO Benchmark
noloop = $$(buildBenchmark prog11 [50,100,150,200,250,300] "noloop")

benchLoopD :: IO Benchmark
benchLoopD = $$(buildBenchmark loopD [50,100,150,200,250,300] "loopD")

benchLoopM :: IO Benchmark
benchLoopM = $$(buildBenchmark loopM [50,100,150,200,250,300] "loopM")

benchLoopDLoopM :: IO Benchmark
benchLoopDLoopM = $$(buildBenchmark loopDloopM [50,100,150,200,250,300] "loopDloopM")