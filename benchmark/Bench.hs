module Main where

import BenchRandom

-- RUN WITH
-- stack build loop-compile:bench:bench-vs-yampa

main :: IO ()
main = benchRandom
