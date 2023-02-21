{-# LANGUAGE DataKinds, GADTs #-}

module ProgramGen where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import TestHelpers

import ArrowCF
import FRP.Yampa (SF, iPre)
import qualified Control.Arrow as A
import qualified Control.Category as C
import LoopGen

-- TODO: nesting within the decoupled bits.
makeMassiveNestedLoop :: Int -> Gen (CF (V Int) (V Int), SF Int Int)
makeMassiveNestedLoop 0 = Gen.constant (id_, C.id)
makeMassiveNestedLoop d = Gen.choice [
        do
            -- LoopD
            pairLen <- Gen.integral (Range.linear 1 10)
            singleLen <- Gen.integral (Range.linear 1 5)
            (cfmain, sfmain) <- genPairProg pairLen
            (cftail, sftail) <- genSingleProg singleLen
            (del, del') <- genOneVal
            (cfnest, sfnest) <- makeMassiveNestedLoop (d-1)
            Gen.choice [
                return (
                    loop $ cfmain >>> second (pre del >>> cfnest >>> cftail),
                    A.loop $ sfmain A.>>> A.second (iPre del' A.>>> sfnest A.>>> sftail)),
                return (
                    loop $ cfmain >>> (cfnest *** (pre del >>> cftail)),
                    A.loop $ sfmain A.>>> (sfnest A.*** (iPre del' A.>>> sftail))),
                return (
                    loop $ second (cfnest >>> pre del >>> cftail) >>> cfmain,
                    A.loop $ A.second (sfnest A.>>> iPre del' A.>>> sftail) A.>>> sfmain
                )
                ],
        do
            -- LoopM
            leftLen <- Gen.integral (Range.linear 1 5)
            rightLen <- Gen.integral (Range.linear 1 5)
            (cfleft, sfleft) <- genPairProg leftLen
            (cfright, sfright) <- genPairProg rightLen
            (del, del') <- genPairVal
            (cfnest, sfnest) <- makeMassiveNestedLoop (d-1)
            Gen.choice [
                return (
                    loop $ cfleft >>> first cfnest >>> pre del >>> cfright,
                    A.loop $ sfleft A.>>> A.first sfnest A.>>> iPre del' A.>>> sfright),
                return (
                    loop $ cfleft >>> pre del >>> second cfnest >>> cfright,
                    A.loop $ sfleft A.>>> iPre del' A.>>> A.second sfnest A.>>> sfright)
                ]

    ]

genInputSamples :: Int -> Gen ([Val (V Int)], [Int])
genInputSamples i = unzip <$> Gen.list (Range.singleton i) genOneVal

simplify :: Val (V Int) -> Int
simplify (One x) = x