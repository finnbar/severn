{-# LANGUAGE DataKinds #-}

module ProgramGen where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import TestHelpers

import ArrowNF
import FRP.Yampa (SF, iPre)
import qualified Control.Arrow as A

makeLargeLoopsRight :: Gen (ANF (V Int) (V Int), SF Int Int)
makeLargeLoopsRight = do
    (anfmain, sfmain) <- genPairProg 100
    (anftail, sftail) <- genSingleProg 100
    return (loop $ anfmain >>> second (pre (One 0) >>> anftail), A.loop $ sfmain A.>>> A.second (iPre 0 A.>>> sftail))

genInputSamples :: Int -> Gen ([Val (V Int)], [Int])
genInputSamples i = unzip <$> Gen.list (Range.singleton i) genOneVal