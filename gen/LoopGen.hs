{-# LANGUAGE DataKinds, GADTs #-}

module LoopGen where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import ArrowNF
import TestHelpers

import FRP.Yampa (deltaEncode, embed, SF, iPre)
import qualified Control.Arrow as A

mergeANF :: ANF (P (V Int) (V Int)) (V Int)
mergeANF = arr $ \(Pair (One a) (One b)) -> One $ a + b

splitANF :: ANF (V Int) (P (V Int) (V Int))
splitANF = arr $ \(One a) -> Pair (One a) (One a)

mergeSF :: SF (Int, Int) Int
mergeSF = A.arr $ uncurry (+)

splitSF :: SF Int (Int, Int)
splitSF = A.arr $ \x -> (x,x)

makeRightSlider :: Gen (ANF (V Int) (V Int), SF Int Int)
makeRightSlider = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 5)
    (anfmain, sfmain) <- genPairProg pairLen
    (anftail, sftail) <- genSingleProg singleLen
    (del, del') <- genOneVal
    return (loop $ anfmain >>> second (pre del >>> anftail), A.loop $ sfmain A.>>> A.second (iPre del' A.>>> sftail))

makeRightCrusher :: Gen (ANF (V Int) (V Int), SF Int Int)
makeRightCrusher = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 2)
    (anfmain, sfmain) <- genPairProg pairLen
    (anftail, sftail) <- genSingleProg singleLen
    (crush, crush') <- genCrushable
    let anf = loop $ anfmain >>> second (splitANF >>> crush >>> mergeANF >>> anftail)
        sf = A.loop $ sfmain A.>>> A.second (splitSF A.>>> crush' A.>>> mergeSF A.>>> sftail)
    return (anf, sf)

makeLeftSlider :: Gen (ANF (V Int) (V Int), SF Int Int)
makeLeftSlider = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 5)
    (anfmain, sfmain) <- genPairProg pairLen
    (anfhead, sfhead) <- genSingleProg singleLen
    (del, del') <- genOneVal
    return (loop $ second (anfhead >>> pre del) >>> anfmain, A.loop $ A.second (sfhead A.>>> iPre del') A.>>> sfmain)

makeLoopM :: Gen (ANF (V Int) (V Int), SF Int Int)
makeLoopM = do
    leftLen <- Gen.integral (Range.linear 1 3)
    rightLen <- Gen.integral (Range.linear 1 3)
    (anfleft, sfleft) <- genPairProg leftLen
    (anfright, sfright) <- genPairProg rightLen
    (del, del') <- genPairVal
    return (
            loop $ anfleft >>> pre del >>> anfright,
            A.loop $ sfleft A.>>> iPre del' A.>>> sfright
        )