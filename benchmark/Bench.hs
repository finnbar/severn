{-# LANGUAGE BangPatterns #-}

module Main where

-- RUN WITH
-- stack build loop-compile:bench:bench-vs-yampa

import Criterion
import Criterion.Main
import Hedgehog.Gen (sample)

import FRP.Yampa
import Transform
import ProgramGen
import TestHelpers
import Run

main :: IO ()
main = do
    (!anf, !sf) <- sample $ makeMassiveNestedLoop 100
    let !anf' = transform anf
    !canf <- compile anf'
    --(anf100, sf100) <- sample $ genInputSamples 100
    (anf1000, sf1000) <- sample $ genInputSamples 10000
    (anf10000, sf10000) <- sample $ genInputSamples 100000
    defaultMain [
            bgroup "anf" [
                --bench "100" $ nf (map simplify . multiRun runanf anf) anf100,
                bench "10000" $ nf (map simplify . multiRun runANF anf') anf1000,
                bench "100000" $ nf (map simplify . multiRun runANF anf') anf10000
            ],
            bgroup "sf" [
                --bench "100" $ nf (embed sf) (deltaEncode 1 sf100),
                bench "1000" $ nf (embed sf) (deltaEncode 1 sf1000),
                bench "10000" $ nf (embed sf) (deltaEncode 1 sf10000)
            ]
        ]