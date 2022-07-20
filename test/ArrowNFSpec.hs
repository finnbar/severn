{-# LANGUAGE TemplateHaskell, DataKinds, FlexibleContexts,
    OverloadedStrings, GADTs, PolyKinds, ExplicitForAll #-}

module ArrowNFSpec (arrowNFSpec) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import TestHelpers

import ArrowAST
import ArrowNF (ANF, Desc(..), Val(..), runANF)

-- * Test ANF vs reference implementation.

checkEqual :: forall k (a :: Desc k) (b :: Desc k). (Eq (Val a), Eq (Val b), Show (Val b)) =>
    ArrowAST a b -> [Val a] -> PropertyT IO ()
checkEqual prog ins =
    multiRun runArrowAST prog ins === multiRun runANF (toANF prog) ins

-- Basic check that `arr` works like in the reference implementation.
prop_check_arr_matches :: Property
prop_check_arr_matches = property $ do
    inps <- forAll genOnes
    checkEqual (arrAST (+1)) inps

-- Check that a simple loop works like the reference implementation.
prop_simple_loop :: Property
prop_simple_loop = property $ do
    inps <- forAll genOnes
    let prog = Loop (arrAST2 (\(a,b) -> (a+b, a)) :>>>: Second (preAST 0))
    checkEqual prog inps

-- Check that `***` works like the reference implementation.
prop_par :: Property
prop_par = property $ do
    inps <- forAll genPairs
    checkEqual (arrAST (+1) :***: arrAST (+2)) inps

-- Check that (f >>> g) *** (h >>> i) works. This is relevant because our
-- implementation transforms this to (f *** h) >>> (g *** i).
prop_distribute :: Property
prop_distribute = property $ do
    inps <- forAll genPairs
    let prog = (arrAST (+1) :>>>: arrAST (+2)) :***: (arrAST (+3) :>>>: arrAST (+4))
    checkEqual prog inps

-- Check that the above also works with `pre` (which updates internal state).
prop_distribute_pre :: Property
prop_distribute_pre = property $ do
    inps <- forAll genPairs
    let prog = (arrAST (+1) :>>>: preAST 0) :***: (preAST 0 :>>>: arrAST (+4))
    checkEqual prog inps

-- Check that `first` and `second` work accordingly.
prop_first_second :: Property
prop_first_second = property $ do
    inps <- forAll genPairs
    let prog = First (arrAST (+1)) :>>>: Second (arrAST (+2))
    checkEqual prog inps

-- Check that a loop inside a loop works.
prop_loop_in_loop :: Property
prop_loop_in_loop = property $ do
    inps <- forAll genOnes
    let prog = Loop (Loop (arrAST21 (\((a,c),b) -> ((a+b,c),a)) 
            :>>>: Second (preAST 0)) :>>>: Second (preAST 0))
    checkEqual prog inps

-- Checks that a composition of loops, where neither loop affects the other, works.
prop_loop_in_loop_composed :: Property
prop_loop_in_loop_composed = property $ do
    inps <- forAll genOnes
    let prog = Loop (First (Loop (arrAST2 (\(a,b) -> (a+b, a)) :>>>: Second (preAST 0)))
                :>>>: Second (Loop (arrAST2 (\(a,b) -> (a+b, a)) :>>>: Second (preAST 0)))
                :>>>: Second (preAST 0))
    checkEqual prog inps

-- Checks that a composition of loops, where the result of one is used in the other, works.
prop_loop_in_loop_related :: Property
prop_loop_in_loop_related = property $ do
    inps <- forAll genOnes
    let progs = Loop (First (Loop (arrAST2 (\(a,b) -> (a+b, a)) :>>>: Second (preAST 0)))
                :>>>: Arr (\(Pair (One a) (One b)) -> One $ a + b)
                :>>>: Loop (arrAST2 (\(a,b) -> (a+b, a)) :>>>: Second (preAST 0))
                :>>>: Arr (\x -> Pair x x)
                :>>>: Second (preAST 0))
    checkEqual progs inps

arrowNFSpec :: Group
arrowNFSpec = $$(discover) {groupName = "ArrowNF matches its reference implementation"}