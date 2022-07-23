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

prop_transform_noloop :: Property
prop_transform_noloop = property $ do
    (ins, ins') <- forAll genPairVals
    len <- forAll $ Gen.integral (Range.linear 1 10)
    (anf, sf) <- forAllWith (show . fst) $ genPairProg len
    checkEqual (transform anf, sf) (ins, ins')

prop_transform_trivial :: Property
prop_transform_trivial = property $ do
    (ins, ins') <- forAll genOneVals
    len <- forAll $ Gen.integral (Range.linear 1 10)
    (anf, sf) <- forAllWith (show . fst) $ genPairProg len
    (del, del') <- forAll genOneVal
    checkEqual (transform $ loop $ anf >>> second (pre del), A.loop $ sf A.>>> A.second (iPre del')) (ins, ins')

prop_right_slide :: Property
prop_right_slide = property $ do
    (ins, ins') <- forAll genOneVals
    pairLen <- forAll $ Gen.integral (Range.linear 1 10)
    singleLen <- forAll $ Gen.integral (Range.linear 1 5)
    (anfmain, sfmain) <- forAllWith (show . fst) $ genPairProg pairLen
    (anftail, sftail) <- forAllWith (show . fst) $ genSingleProg singleLen
    (del, del') <- forAll genOneVal
    checkEqual (transform $ loop $ anfmain >>> second (pre del >>> anftail), A.loop $ sfmain A.>>> A.second (iPre del' A.>>> sftail)) (ins, ins')

-- TODO: A few more tests.
-- * A test requiring a larger pre, so second (pre (i,j))
-- * A test requiring right crush, so second (first pre >>> second pre)
-- * (once implemented) a test requiring left slide (second pre >>> arr2)

transformSpec :: Group
transformSpec = $$(discover) {groupName = "Transform produces equivalent programs"}