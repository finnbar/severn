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

-- * Make sure that ArrowNF upholds the properties we set about it.

-- Check that (f >>> g) *** (h >>> i) works [LHS]. This is relevant because our
-- implementation transforms this to (f *** h) >>> (g *** i) [RHS].
prop_distribute :: Property
prop_distribute = property $ do
    len <- forAll $ Gen.integral (Range.linear 1 20)
    (lhs, rhs) <- forAll $ genDistributiveTest len
    lhs === rhs

-- Make sure that Id >>> f ==> f <== f >>> Id
prop_no_id :: Property
prop_no_id = property $ do
    len <- forAll $ Gen.integral (Range.linear 1 50)
    (clean, dirty) <- forAll $ genNCompsWithId len
    clean === dirty

-- Make sure that Pre (i,j) ==> Pre i *** Pre j
prop_no_pre_pairs :: Property
prop_no_pre_pairs = property $ do
    len <- forAll $ Gen.integral (Range.linear 1 50)
    (clean, dirty) <- forAll $ genNCompsWithPrePairs len
    clean === dirty

arrowNFSpec :: Group
arrowNFSpec = $$(discover) {groupName = "ArrowNF invariants hold"}