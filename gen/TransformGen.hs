{-# LANGUAGE DataKinds, GADTs #-}

module LoopGen where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import ArrowCF
import TestHelpers

import FRP.Yampa (deltaEncode, embed, SF, iPre)
import qualified Control.Arrow as A

mergeCF :: CF (P (V Int) (V Int)) (V Int)
mergeCF = arr $ \(Pair (One a) (One b)) -> One $ a + b

splitCF :: CF (V Int) (P (V Int) (V Int))
splitCF = arr $ \(One a) -> Pair (One a) (One a)

mergeSF :: SF (Int, Int) Int
mergeSF = A.arr $ uncurry (+)

splitSF :: SF Int (Int, Int)
splitSF = A.arr $ \x -> (x,x)

makeRightSlider :: Gen (CF (V Int) (V Int), SF Int Int)
makeRightSlider = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 5)
    (cfmain, sfmain) <- genPairProg pairLen
    (cftail, sftail) <- genSingleProg singleLen
    (del, del') <- genOneVal
    return (loop $ cfmain >>> second (pre del >>> cftail), A.loop $ sfmain A.>>> A.second (iPre del' A.>>> sftail))

makeRightCrusher :: Gen (CF (V Int) (V Int), SF Int Int)
makeRightCrusher = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 2)
    (cfmain, sfmain) <- genPairProg pairLen
    (cftail, sftail) <- genSingleProg singleLen
    (crush, crush') <- genCrushable
    let cf = loop $ cfmain >>> second (splitCF >>> crush >>> mergeCF >>> cftail)
        sf = A.loop $ sfmain A.>>> A.second (splitSF A.>>> crush' A.>>> mergeSF A.>>> sftail)
    return (cf, sf)

makeLeftSlider :: Gen (CF (V Int) (V Int), SF Int Int)
makeLeftSlider = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 5)
    (cfmain, sfmain) <- genPairProg pairLen
    (cfhead, sfhead) <- genSingleProg singleLen
    (del, del') <- genOneVal
    return (loop $ second (cfhead >>> pre del) >>> cfmain, A.loop $ A.second (sfhead A.>>> iPre del') A.>>> sfmain)

makeLoopM :: Gen (CF (V Int) (V Int), SF Int Int)
makeLoopM = do
    leftLen <- Gen.integral (Range.linear 1 3)
    rightLen <- Gen.integral (Range.linear 1 3)
    (cfleft, sfleft) <- genPairProg leftLen
    (cfright, sfright) <- genPairProg rightLen
    (del, del') <- genPairVal
    return (
            loop $ cfleft >>> pre del >>> cfright,
            A.loop $ sfleft A.>>> iPre del' A.>>> sfright
        )