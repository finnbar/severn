{-# LANGUAGE BangPatterns #-}

module Main where

import Criterion
import Criterion.Main
import Hedgehog.Gen (sample)

import FRP.Yampa
import qualified Control.Arrow as A
import Transform
import ProgramGen
import TestHelpers

-- TODO: These tests are too small to give meaningful results. Increase something.
main :: IO ()
main = do
    (!anf, !sf) <- sample makeLargeLoopsRight
    let !alp = transform anf
    (alp10, sf10) <- sample $ genInputSamples 10
    (alp100, sf100) <- sample $ genInputSamples 100
    (alp1000, sf1000) <- sample $ genInputSamples 1000
    (alp10000, sf10000) <- sample $ genInputSamples 10000
    defaultMain [
            bgroup "alp" [
                bench "10" $ whnf (multiRun runALP alp) alp10,
                bench "100" $ whnf (multiRun runALP alp) alp100,
                bench "1000" $ whnf (multiRun runALP alp) alp1000,
                bench "10000" $ whnf (multiRun runALP alp) alp10000
            ],
            bgroup "sf" [
                bench "10" $ whnf (embed sf) (deltaEncode 1 sf10),
                bench "100" $ whnf (embed sf) (deltaEncode 1 sf100),
                bench "1000" $ whnf (embed sf) (deltaEncode 1 sf1000),
                bench "10000" $ whnf (embed sf) (deltaEncode 1 sf10000)
            ]
        ]