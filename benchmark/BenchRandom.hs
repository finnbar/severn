{-# LANGUAGE BangPatterns, DataKinds #-}

module BenchRandom (benchRandom) where

import Criterion
import Hedgehog (Gen)
import Hedgehog.Gen (sample)
import Control.DeepSeq
import Data.IORef
import Control.Monad (forM)
import System.IO (Handle, hFlush, stderr, stdout, hPutStr)

import BenchHelpers
import ArbitraryProgram
import TestHelpers

benchRandom :: IO Benchmark
benchRandom = do
    cPSL "Running"
    !inputs <- sample $ genDoubles 100000 --genInputSamples 100000
    let sizes = [50,100,150,200,250,300]
    cPSL "Generating loopProportion=0.1"
    loop10 <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0.1)) inputs
    cPSL "Generating loopProportion=0.25"
    loop25 <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0.25)) inputs
    cPSL "Generating loopProportion=0.5"
    loop50 <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0.5)) inputs
    cPSL "Done generating"
    let !benches = [bgroup "lp=0.1" loop10, bgroup "lp=0.25" loop25, bgroup "lp=0.5" loop50]
    return $ bgroup "Random benchmarks" benches