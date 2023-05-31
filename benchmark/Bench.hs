module Main where

import BenchRandom
import BenchTHTests

import Criterion.Main
import Criterion.Types (Config(..), Verbosity(..))
import Statistics.Types (cl99)

-- RUN WITH
-- stack build loop-compile:bench:bench-vs-yampa

main :: IO ()
main = do
    th <- benchTHTests
    rd <- benchRandom
    let benches = [th]
    defaultMainWith (defaultConfig {csvFile = Just "tests-no-timeout.csv", confInterval = cl99, timeLimit = 2000, verbosity = Verbose}) benches
