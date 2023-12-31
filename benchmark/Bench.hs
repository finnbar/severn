module Main where

import BenchRandom
import BenchTHTests

import Criterion.Main
import Criterion.Types (Config(..), Verbosity(..))
import Statistics.Types (cl99)

-- RUN WITH
-- stack build loop-compile:bench:bench-vs-yampa

main :: IO ()
main = randomAndTH
    
randomAndTH :: IO ()
randomAndTH = do
    th <- benchTHTests
    rd <- benchRandom
    let benches = [th, rd]
    defaultMainWith (defaultConfig {csvFile = Just "tests.csv", confInterval = cl99, timeLimit = 20, verbosity = Verbose}) benches

randomOnly :: IO ()
randomOnly = do
    rd <- benchRandom
    defaultMainWith (defaultConfig {csvFile = Just "tests-random.csv", timeLimit = 20}) [rd]
