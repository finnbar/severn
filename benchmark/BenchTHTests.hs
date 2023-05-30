{-# LANGUAGE TemplateHaskell, GADTs, DataKinds #-}

module BenchTHTests where

import TestPrograms
import ProgGenTH
import CFSF

import Criterion
import Criterion.Types
import Criterion.Main

benchTHTests :: IO Benchmark
benchTHTests = do
    nl <- noloop
    ld <- benchLoopD
    lm <- benchLoopM
    ldlm <- benchLoopDLoopM
    mpl <- benchManyPreLoop
    let benches = [nl, ld, lm, ldlm, mpl]
    return $ bgroup "THTests" benches

noloop :: IO Benchmark
noloop = $$(buildBenchmark prog11 [50,100,150,200,250,300] "noloop")

benchLoopD :: IO Benchmark
benchLoopD = $$(buildBenchmark loopD [50,100,150,200,250,300] "loopD")

benchLoopM :: IO Benchmark
benchLoopM = $$(buildBenchmark loopM [50,100,150,200,250,300] "loopM")

benchLoopDLoopM :: IO Benchmark
benchLoopDLoopM = $$(buildBenchmark loopDloopM [50,100,150,200,250,300] "loopDloopM")

benchManyPreLoop :: IO Benchmark
benchManyPreLoop = $$(buildBenchmark manyPreLoop [50,100,150,200,250,300] "manyPreLoop")