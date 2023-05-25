module Main where

import BenchRandom
import BenchTHTests

-- RUN WITH
-- stack build loop-compile:bench:bench-vs-yampa

main :: IO ()
main = benchTHTests
