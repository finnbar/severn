{-# LANGUAGE TemplateHaskell, DataKinds, FlexibleContexts,
    OverloadedStrings, GADTs, PolyKinds, ExplicitForAll #-}

module ArrowNFSpec (arrowNFSpec) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Proxy (Proxy(..))

import ArrowNF
import ArrowNFGen
import TestHelpers

-- TODO: Rewrite these tests now that ArrowNF has changed significantly.

-- * Make sure that ArrowNF upholds the properties we set about it.
-- Also make sure the Loop laws continue to hold.

-- Check that (f >>> g) *** (h >>> i) works [LHS]. This is relevant because our
-- implementation transforms this to (f *** h) >>> (g *** i) [RHS].
prop_distribute :: Property
prop_distribute = property $ do
    len <- forAll $ Gen.integral (Range.linear 1 20)
    (lhs, rhs) <- forAll $ genDistributiveTest len
    lhs === rhs

-- -- Make sure that Id >>> f ==> f <== f >>> Id
-- prop_no_id :: Property
-- prop_no_id = property $ do
--     len <- forAll $ Gen.integral (Range.linear 1 50)
--     (clean, dirty) <- forAll $ genNCompsWithId len
--     clean === dirty

-- -- Make sure that Id *** Id ==> Id
-- prop_no_pair_id :: Property
-- prop_no_pair_id = property $ do
--     len <- forAll $ Gen.integral (Range.linear 1 50)
--     (clean, dirty) <- forAll $ genNCompsWithPairId len
--     clean === dirty

-- -- Make sure that Pre (i,j) ==> Pre i *** Pre j
-- -- NOTE: our Eq check doesn't check the contents of pre, so this test only
-- -- checks that a Pre pair is replaced with a single Pre.
-- prop_no_pre_pairs :: Property
-- prop_no_pre_pairs = property $ do
--     len <- forAll $ Gen.integral (Range.linear 1 50)
--     (clean, dirty) <- forAll $ genNCompsWithPrePairs len
--     clean === dirty

-- -- Make sure that right crunch is being obeyed, that is:
-- -- (a *** b) >>> (c *** id) = (a *** id) >>> (c *** b)
-- -- and
-- -- (a *** b) >>> (id *** c) = (id *** b) >>> (a *** c)
-- -- This should apply regardless of nesting.
-- prop_right_crunch :: Property
-- prop_right_crunch = property $ do
--     -- We have to specify the sizes of nesting that we work with.
--     -- Therefore, we test a few different sizes.
--     -- Regular sized (common in `loop`)
--     ((lt, rt), (lt', rt')) <- forAll $
--         genCrunchTrees (Proxy :: Proxy ('P ('V Int) ('V Int)))
--     lt >>> rt === lt' >>> rt'
--     -- Large (uncommon)
--     ((lt2, rt2), (lt2', rt2')) <- forAll $
--         genCrunchTrees (Proxy :: Proxy ('P ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int))))
--     lt2 >>> rt2 === lt2' >>> rt2'
--     -- Unbalanced (similar to Assoc)
--     ((lt3, rt3), (lt3', rt3')) <- forAll $
--         genCrunchTrees (Proxy :: Proxy ('P ('P ('V Int) ('V Int)) ('V Int)))
--     lt3 >>> rt3 === lt3' >>> rt3'

-- prop_loop_left_tightening :: Property
-- prop_loop_left_tightening = property $ do
--     len1 <- forAll $ Gen.integral (Range.linear 1 20)
--     len2 <- forAll $ Gen.integral (Range.linear 1 20)
--     h <- forAll $ fst <$> genSingleProg len1
--     f <- forAll $ fst <$> genPairProg len2
--     loop (first h >>> f) === h >>> loop f

-- prop_loop_right_tightening :: Property
-- prop_loop_right_tightening = property $ do
--     len1 <- forAll $ Gen.integral (Range.linear 1 20)
--     len2 <- forAll $ Gen.integral (Range.linear 1 20)
--     h <- forAll $ fst <$> genSingleProg len1
--     f <- forAll $ fst <$> genPairProg len2
--     loop (f >>> first h) === loop f >>> h

arrowNFSpec :: Group
arrowNFSpec = $$(discover) {groupName = "ArrowNF invariants hold (NEED TO REWRITE THESE TESTS)"}