{-# LANGUAGE DataKinds, GADTs #-}

module ProgramGen where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import TestHelpers

import ArrowNF
import FRP.Yampa (SF, iPre)
import qualified Control.Arrow as A
import qualified Control.Category as C
import LoopGen

makeLargeLoopsRight :: Gen (ANF (V Int) (V Int), SF Int Int)
makeLargeLoopsRight = do
    (anfmain, sfmain) <- genPairProg 100
    (anftail, sftail) <- genSingleProg 100
    return (loop $ anfmain >>> second (pre (One 0) >>> anftail), A.loop $ sfmain A.>>> A.second (iPre 0 A.>>> sftail))

-- TODO: nesting within the decoupled bits.
makeMassiveNestedLoop :: Int -> Gen (ANF (V Int) (V Int), SF Int Int)
makeMassiveNestedLoop 0 = Gen.constant (id_, C.id)
makeMassiveNestedLoop d = Gen.choice [
        do
            -- LoopD
            pairLen <- Gen.integral (Range.linear 1 10)
            singleLen <- Gen.integral (Range.linear 1 5)
            (anfmain, sfmain) <- genPairProg pairLen
            (anftail, sftail) <- genSingleProg singleLen
            (del, del') <- genOneVal
            (anfnest, sfnest) <- makeMassiveNestedLoop (d-1)
            Gen.choice [
                return (
                    loop $ anfmain >>> second (pre del >>> anfnest >>> anftail),
                    A.loop $ sfmain A.>>> A.second (iPre del' A.>>> sfnest A.>>> sftail)),
                return (
                    loop $ anfmain >>> (anfnest *** (pre del >>> anftail)),
                    A.loop $ sfmain A.>>> (sfnest A.*** (iPre del' A.>>> sftail))),
                return (
                    loop $ second (anfnest >>> pre del >>> anftail) >>> anfmain,
                    A.loop $ A.second (sfnest A.>>> iPre del' A.>>> sftail) A.>>> sfmain
                )
                ],
        do
            -- LoopM
            leftLen <- Gen.integral (Range.linear 1 5)
            rightLen <- Gen.integral (Range.linear 1 5)
            (anfleft, sfleft) <- genPairProg leftLen
            (anfright, sfright) <- genPairProg rightLen
            (del, del') <- genPairVal
            (anfnest, sfnest) <- makeMassiveNestedLoop (d-1)
            Gen.choice [
                return (
                    loop $ anfleft >>> first anfnest >>> pre del >>> anfright,
                    A.loop $ sfleft A.>>> A.first sfnest A.>>> iPre del' A.>>> sfright),
                return (
                    loop $ anfleft >>> pre del >>> second anfnest >>> anfright,
                    A.loop $ sfleft A.>>> iPre del' A.>>> A.second sfnest A.>>> sfright)
                ]

    ]

genInputSamples :: Int -> Gen ([Val (V Int)], [Int])
genInputSamples i = unzip <$> Gen.list (Range.singleton i) genOneVal

simplify :: Val (V Int) -> Int
simplify (One x) = x