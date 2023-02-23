{-# LANGUAGE DataKinds, GADTs #-}

module TransformGen where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import ArrowCFSF
import TestHelpers

import FRP.Yampa (deltaEncode, embed, SF, iPre)
import qualified Control.Arrow as A

mergeCFSF :: CFSF (P (V Int) (V Int)) (V Int)
mergeCFSF = arr $ \(Pair (One a) (One b)) -> One $ a + b

splitCFSF :: CFSF (V Int) (P (V Int) (V Int))
splitCFSF = arr $ \(One a) -> Pair (One a) (One a)

mergeSF :: SF (Int, Int) Int
mergeSF = A.arr $ uncurry (+)

splitSF :: SF Int (Int, Int)
splitSF = A.arr $ \x -> (x,x)

makeRightSlider :: Gen (CFSF (V Int) (V Int), SF Int Int)
makeRightSlider = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 5)
    (cfsfmain, sfmain) <- genPairProg pairLen
    (cfsftail, sftail) <- genSingleProg singleLen
    (del, del') <- genOneVal
    return (loop $ cfsfmain >>> second (pre del >>> cfsftail), A.loop $ sfmain A.>>> A.second (iPre del' A.>>> sftail))

makeRightCrusher :: Gen (CFSF (V Int) (V Int), SF Int Int)
makeRightCrusher = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 2)
    (cfsfmain, sfmain) <- genPairProg pairLen
    (cfsftail, sftail) <- genSingleProg singleLen
    (crush, crush') <- genCrushable
    let cfsf = loop $ cfsfmain >>> second (splitCFSF >>> crush >>> mergeCFSF >>> cfsftail)
        sf = A.loop $ sfmain A.>>> A.second (splitSF A.>>> crush' A.>>> mergeSF A.>>> sftail)
    return (cfsf, sf)

makeLeftSlider :: Gen (CFSF (V Int) (V Int), SF Int Int)
makeLeftSlider = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 5)
    (cfsfmain, sfmain) <- genPairProg pairLen
    (cfsfhead, sfhead) <- genSingleProg singleLen
    (del, del') <- genOneVal
    return (loop $ second (cfsfhead >>> pre del) >>> cfsfmain, A.loop $ A.second (sfhead A.>>> iPre del') A.>>> sfmain)

makeLoopM :: Gen (CFSF (V Int) (V Int), SF Int Int)
makeLoopM = do
    leftLen <- Gen.integral (Range.linear 1 3)
    rightLen <- Gen.integral (Range.linear 1 3)
    (cfsfleft, sfleft) <- genPairProg leftLen
    (cfsfright, sfright) <- genPairProg rightLen
    (del, del') <- genPairVal
    return (
            loop $ cfsfleft >>> pre del >>> cfsfright,
            A.loop $ sfleft A.>>> iPre del' A.>>> sfright
        )