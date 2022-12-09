{-# LANGUAGE TemplateHaskell, DataKinds, FlexibleContexts, StandaloneKindSignatures,
    OverloadedStrings, GADTs, PolyKinds, TypeFamilies, ExplicitForAll, BangPatterns #-}

module TransformSpec (transformSpec) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import ArrowNF
import Transform
import TestHelpers
import Run

import FRP.Yampa (deltaEncode, embed, SF, iPre)
import qualified Control.Arrow as A
import System.Timeout
import Control.Monad.IO.Class

-- * Test `transform`.
-- General idea is to test a prewritten program against a Yampa equivalent.

type Simplify :: forall s. Desc s -> *
type family Simplify x where
    Simplify (V a) = a
    Simplify (P a b) = (Simplify a, Simplify b)

removeDesc :: Val a -> Simplify a
removeDesc (One a) = a
removeDesc (Pair a b) = (removeDesc a, removeDesc b)

checkEqualTransform :: (Eq (Simplify a), Eq (Simplify b), Show (Simplify b), ValidDesc a, ValidDesc b) =>
    (ANF a b, SF (Simplify a) (Simplify b)) -> ([Val a], [Simplify a]) -> PropertyT IO ()
checkEqualTransform (anf, sf) (ins, ins') = do
    let sfres = embed sf (deltaEncode 1 ins')
    anf' <- liftIO $ timeout 1000000 $ return $! transform anf
    case anf' of
        Just anf'' -> do
            let anfres = map removeDesc $ multiRun runANF anf'' ins
            sfres === anfres
        Nothing -> footnote "Test timed out." >> failure

-- This makes sure that `transform` leaves programs without loops entirely unaffected.
prop_transform_noloop :: Property
prop_transform_noloop = property $ do
    (ins, ins') <- forAll genPairVals
    len <- forAll $ Gen.integral (Range.linear 1 10)
    (anf, sf) <- forAllWith (show . fst) $ genPairProg len
    checkEqualTransform (anf, sf) (ins, ins')

-- This makes sure that `transform` leaves loops where the `pre` is already in the right place as-is.
prop_transform_trivial :: Property
prop_transform_trivial = property $ do
    (ins, ins') <- forAll genOneVals
    len <- forAll $ Gen.integral (Range.linear 1 10)
    (anf, sf) <- forAllWith (show . fst) $ genPairProg len
    (del, del') <- forAll genOneVal
    checkEqualTransform (loop $ anf >>> second (pre del), A.loop $ sf A.>>> A.second (iPre del')) (ins, ins')

makeRightSlider :: Gen (ANF (V Int) (V Int), SF Int Int)
makeRightSlider = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 5)
    (anfmain, sfmain) <- genPairProg pairLen
    (anftail, sftail) <- genSingleProg singleLen
    (del, del') <- genOneVal
    return (loop $ anfmain >>> second (pre del >>> anftail), A.loop $ sfmain A.>>> A.second (iPre del' A.>>> sftail))

-- This makes sure that simple right slides can be used to move the `pre` into position.
prop_right_slide :: Property
prop_right_slide = property $ do
    (ins, ins') <- forAll genOneVals
    (anf, sf) <- forAllWith (show . fst) makeRightSlider
    checkEqualTransform (anf, sf) (ins, ins')

mergeANF :: ANF (P (V Int) (V Int)) (V Int)
mergeANF = arr $ \(Pair (One a) (One b)) -> One $ a + b

splitANF :: ANF (V Int) (P (V Int) (V Int))
splitANF = arr $ \(One a) -> Pair (One a) (One a)

mergeSF :: SF (Int, Int) Int
mergeSF = A.arr $ uncurry (+)

splitSF :: SF Int (Int, Int)
splitSF = A.arr $ \x -> (x,x)

-- This makes sure that we are able to extract the correct value for a pre even
-- when it is a pair - i.e. a loop ending in second (pre i *** pre j) correctly
-- extracts (i,j).
prop_pre_merge :: Property
prop_pre_merge = property $ do
    (ins, ins') <- forAll genOneVals
    pairLen <- forAll $ Gen.integral (Range.linear 1 10)
    singleLen <- forAll $ Gen.integral (Range.linear 1 2)
    (anfmain, sfmain) <- forAllWith (show . fst) $ genPairProg pairLen
    -- We turn this into the tail by using `second`
    (anftail, sftail) <- forAllWith (show . fst) $ genPairProg singleLen
    (del, del') <- forAll genPairVal
    let anf = loop $ second mergeANF >>> anfmain >>> second (splitANF >>> pre del >>> anftail)
        sf = A.loop $ A.second mergeSF A.>>> sfmain A.>>> A.second (splitSF A.>>> iPre del' A.>>> sftail)
    checkEqualTransform (anf, sf) (ins, ins')

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

-- This makes sure that the right crush property is applied - i.e. if we have
-- (a *** b) >>> (id *** c)
-- we get
-- (id *** b) >>> (a *** c) [and similar for a *** b >>> c *** id]
-- TODO: This test nondeterministically times out.
prop_right_crush :: Property
prop_right_crush = property $ do
    (ins, ins') <- forAll genOneVals
    (anf, sf) <- forAllWith (show . fst) makeRightCrusher
    checkEqualTransform (anf, sf) (ins, ins')

makeLeftSlider :: Gen (ANF (V Int) (V Int), SF Int Int)
makeLeftSlider = do
    pairLen <- Gen.integral (Range.linear 1 10)
    singleLen <- Gen.integral (Range.linear 1 5)
    (anfmain, sfmain) <- genPairProg pairLen
    (anfhead, sfhead) <- genSingleProg singleLen
    (del, del') <- genOneVal
    return (loop $ second (anfhead >>> pre del) >>> anfmain, A.loop $ A.second (sfhead A.>>> iPre del') A.>>> sfmain)

-- This makes sure that simple left slides can be used to move the `pre` into position.
prop_left_slide :: Property
prop_left_slide = property $ do
    (ins, ins') <- forAll genOneVals
    (anf, sf) <- forAllWith (show . fst) makeLeftSlider
    checkEqualTransform (anf, sf) (ins, ins')

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

prop_loopM :: Property
prop_loopM = property $ do
    (ins, ins') <- forAll genOneVals
    (anf, sf) <- forAllWith (show . fst) makeLoopM
    checkEqualTransform (anf, sf) (ins, ins')

-- Two right sliding loops, one inside another. They each have their own $pre$.
prop_loop_in_loop :: Property
prop_loop_in_loop = property $ do
    (ins, ins') <- forAll genOneVals
    (anfinner, sfinner) <- forAllWith (show . fst) $ Gen.choice [makeRightSlider, makeLeftSlider]
    len <- forAll $ Gen.integral (Range.linear 1 3)
    len' <- forAll $ Gen.integral (Range.linear 1 3)
    (anfextra, sfextra) <- forAllWith (show . fst) $ genSingleProg len
    (anf, sf) <- forAllWith (show . fst) $ Gen.element [
            (loop $ first anfinner >>> second (pre (One 0) >>> anfextra),
                A.loop $ A.first sfinner A.>>> A.second (iPre 0 A.>>> sfextra))
        ]
    checkEqualTransform (anf, sf) (ins, ins')

-- Make sure a pair of loops works.
prop_pair_loop :: Property
prop_pair_loop = property $ do
    (ins, ins') <- forAll genPairVals
    (anfleft, sfleft) <- forAllWith (show . fst) makeRightSlider
    (anfright, sfright) <- forAllWith (show . fst) makeRightSlider
    let anf = anfleft *** anfright
        sf = sfleft A.*** sfright
    checkEqualTransform (anf, sf) (ins, ins')

-- Test where an inner loop acts as the pre for an outer loop
-- TODO: can we make a more complex version of this? e.g. when there's other things to tighten before the pre,
-- when it's at the front of the loop instead of the back etc.
prop_depends_pre :: Property
prop_depends_pre = property $ do
    (ins, ins') <- forAll genOneVals 
    len <- forAll $ Gen.integral (Range.linear 1 3)
    len' <- forAll $ Gen.integral (Range.linear 1 3)
    (anfinner, sfinner) <- forAllWith (show . fst) $ genPairProg len
    (anfouter, sfouter) <- forAllWith (show . fst) $ genPairProg len'
    (anfdel, sfdel) <- forAll genPairVal 
    let anf = loop (anfouter >>> second (loop (anfinner >>> pre anfdel)))
        sf = A.loop (sfouter A.>>> A.second (A.loop (sfinner A.>>> iPre sfdel)))
    checkEqualTransform (anf, sf) (ins, ins')

-- Test where an inner LoopM is the pre of an outer loop.
-- TODO: a test where it's a mix of Pre and LoopM
prop_depends_loopM :: Property
prop_depends_loopM = property $ do
    (ins, ins') <- forAll genOneVals
    (anf, sf) <- forAllWith (show . fst) makeLoopM
    len <- forAll $ Gen.integral (Range.linear 1 3)
    (anfouter, sfouter) <- forAllWith (show . fst) $ genPairProg len
    let anf' = loop (anfouter >>> second anf)
        sf' = A.loop (sfouter A.>>> A.second sf)
    checkEqualTransform (anf', sf') (ins, ins')

-- TODO: benchmarks! Compare a large SF vs its ALP version.

transformSpec :: Group
transformSpec = $$(discover) {groupName = "Transform produces equivalent programs"}