{-# LANGUAGE TemplateHaskell, DataKinds, FlexibleContexts,
    OverloadedStrings, GADTs #-}

module TransformSpec (transformSpec) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import ArrowNF
import Transform

-- * Test `transform`.
-- General idea is to test a prewritten program against a Yampa equivalent.

{-
checkEqual :: (Eq (Val b), Show (Val b)) => ANF a b -> [Val a] -> PropertyT IO ()
checkEqual prog = checkEqual' (prog, transform prog)

checkEqual' :: (Eq (Val b), Show (Val b)) => (ANF a b, ALP a b) -> [Val a] -> PropertyT IO ()
checkEqual' (anf, alp) ins =
    multiRun runANF anf ins === multiRun runALP alp ins

complexNoLoop :: ANF (V Int) (V Int)
complexNoLoop = arr (\(One a) -> One (a+2)) >>> arr (\x -> Pair x x)
    >>> arr (\(Pair (One a) (One b)) -> One (a + b))

prop_transform_noloop :: Property
prop_transform_noloop = property $ do
    inps <- forAll genOneVals
    checkEqual complexNoLoop inps

prop_transform_rightslide :: Property 
prop_transform_rightslide = property $ do
    inps <- forAll genOneVals
    delay <- forAll genOne
    let prog = loop (arr (\(Pair (One x) (One y)) -> Pair (One $ x+y) (One x)) >>> second (pre delay) >>> second complexNoLoop)
    checkEqual prog inps

prop_transform_complexrouting :: Property
prop_transform_complexrouting = property $ do
    inps <- forAll genOneVals
    delay <- forAll genOne
    -- Funnily enough, the transformed version doesn't need the strictness annotations.
    let prog = loop (arr fn
            >>> second (first (pre delay) >>> second (pre delay)))
    checkEqual prog inps
    where
        fn :: Val (P (V Int) (P (V Int) (V Int))) -> Val (P (V Int) (P (V Int) (V Int)))
        fn (Pair (One x) (Pair (One y) (One z))) = Pair (One $ x + y) (Pair (One x) (One z))

prop_transform_bigpre :: Property
prop_transform_bigpre = property $ do
    inps <- forAll genOneVals
    delay <- forAll genOne
    delay' <- forAll genOne
    let prog = loop (arr (\(Pair (One x) (One y)) -> Pair (One $ x+y) (One x)) >>> pre (Pair delay delay') >>> second complexNoLoop)
    checkEqual prog inps
-}
transformSpec :: Group
transformSpec = $$(discover) {groupName = "Transform produces equivalent programs"}