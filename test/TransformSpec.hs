{-# LANGUAGE TemplateHaskell, DataKinds, FlexibleContexts, StandaloneKindSignatures,
    OverloadedStrings, GADTs, PolyKinds, TypeFamilies, ExplicitForAll #-}

module TransformSpec (transformSpec) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import ArrowNF
import Transform
import TestHelpers

import FRP.Yampa (deltaEncode, embed, SF, iPre)
import qualified Control.Arrow as A

-- * Test `transform`.
-- General idea is to test a prewritten program against a Yampa equivalent.

type Simplify :: forall s. Desc s -> *
type family Simplify x where
    Simplify (V a) = a
    Simplify (P a b) = (Simplify a, Simplify b)

removeDesc :: Val a -> Simplify a
removeDesc (One a) = a
removeDesc (Pair a b) = (removeDesc a, removeDesc b)

checkEqual :: (Eq (Simplify a), Eq (Simplify b), Show (Simplify b)) =>
    (ALP a b, SF (Simplify a) (Simplify b)) -> ([Val a], [Simplify a]) -> PropertyT IO ()
checkEqual (alp, sf) (ins, ins') =
    let sfres = embed sf (deltaEncode 1 ins')
        alpres = map removeDesc $ multiRun runALP alp ins
    in sfres === alpres

-- This makes sure that `transform` leaves programs without loops entirely unaffected.
prop_transform_noloop :: Property
prop_transform_noloop = property $ do
    (ins, ins') <- forAll genPairVals
    len <- forAll $ Gen.integral (Range.linear 1 10)
    (anf, sf) <- forAllWith (show . fst) $ genPairProg len
    checkEqual (transform anf, sf) (ins, ins')

-- This makes sure that `transform` leaves loops where the `pre` is already in the right place as-is.
prop_transform_trivial :: Property
prop_transform_trivial = property $ do
    (ins, ins') <- forAll genOneVals
    len <- forAll $ Gen.integral (Range.linear 1 10)
    (anf, sf) <- forAllWith (show . fst) $ genPairProg len
    (del, del') <- forAll genOneVal
    checkEqual (transform $ loop $ anf >>> second (pre del), A.loop $ sf A.>>> A.second (iPre del')) (ins, ins')

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
    checkEqual (transform anf, sf) (ins, ins')

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
    let anf = transform $ loop $ second mergeANF >>> anfmain >>> second (splitANF >>> pre del >>> anftail)
        sf = A.loop $ A.second mergeSF A.>>> sfmain A.>>> A.second (splitSF A.>>> iPre del' A.>>> sftail)
    checkEqual (anf, sf) (ins, ins')

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
prop_right_crush :: Property
prop_right_crush = property $ do
    (ins, ins') <- forAll genOneVals
    (anf, sf) <- forAllWith (show . fst) makeRightCrusher
    checkEqual (transform anf, sf) (ins, ins')

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
    checkEqual (transform anf, sf) (ins, ins')

-- Make sure transform works where a squish is required - i.e. a 2in 2out pre.
prop_squish_required :: Property
prop_squish_required = property $ do
    (ins, ins') <- forAll genOneVals
    leftLen <- forAll $ Gen.integral (Range.linear 1 3)
    rightLen <- forAll $ Gen.integral (Range.linear 1 3)
    (anfleft, sfleft) <- forAllWith (show . fst) $ genPairProg leftLen
    (anfright, sfright) <- forAllWith (show . fst) $ genPairProg rightLen
    (del, del') <- forAll genPairVal
    checkEqual (transform $ loop $ anfleft >>> pre del >>> anfright, A.loop $ sfleft A.>>> iPre del' A.>>> sfright) (ins, ins')

-- TODO: Loop in loop, where each loop has its own delay. This makes sure that our use of Assoc and Cossa doesn't break anything.
-- Both loops are solvable individually via right sliding.
-- NOTE: It turns out that Assoc etc do break something...
-- Also this test currently assumes that both loops are solvable via right sliding - we need a mix.
prop_loop_in_loop :: Property
prop_loop_in_loop = property $ do
    (ins, ins') <- forAll genOneVals
    (anfinner, sfinner) <- forAllWith (show . fst) makeRightSlider
    len <- forAll $ Gen.integral (Range.linear 1 3)
    len' <- forAll $ Gen.integral (Range.linear 1 3)
    (anfextra, sfextra) <- forAllWith (show . fst) $ genSingleProg len
    (anf, sf) <- forAllWith (show . fst) $ Gen.element [
            (loop $ first anfinner >>> second (pre (One 0) >>> anfextra),
                A.loop $ A.first sfinner A.>>> A.second (iPre 0 A.>>> sfextra))
        ]
    alp <- eval $ transform anf
    checkEqual (alp, sf) (ins, ins')

-- TODO: tests for first (loop f) and others that require Distributive and Juggle.
-- TODO: test where an inner loop acts as the pre for an outer loop

-- TODO: benchmarks! Compare a large SF vs its ALP version.

transformSpec :: Group
transformSpec = $$(discover) {groupName = "Transform produces equivalent programs"}