{-# LANGUAGE DataKinds, GADTs, PolyKinds, ScopedTypeVariables,
    StandaloneKindSignatures, FlexibleInstances #-}

module ArrowCFSFGen where

import Prelude hiding (id)

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Kind (Constraint)
import Data.Proxy (Proxy(..))

import ArrowCFSF
import TestHelpers

-- Generates a pair of CFSFs: one of the form
-- ((a1 >>> ... >>> z1) *** (a2 >>> ... >>> z2))
-- and another of the form
-- ((a1 *** a2) >>> ... >>> (z1 *** z2)).
-- We use this in @prop_distribute@.
genDistributiveTest :: Int ->
    Gen (CFSF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)),
        CFSF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)))
genDistributiveTest n
    | n <= 0 = undefined
    | otherwise = do
        ((l,r),lr) <- genNComposition n
        return (l *** r, lr)
    where
        -- LHS of tuple = (l, r) to eventually be l *** r
        -- RHS of tuple = lr which is each (l *** r) composed
        genNComposition :: Int ->
            Gen ((CFSF ('V Int) ('V Int), CFSF ('V Int) ('V Int)),
                CFSF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)))
        genNComposition 1 = do
            f <- fst <$> genSingle
            f' <- fst <$> genSingle
            return ((f, f'), f *** f')
        genNComposition n = do
            ((l, r),lr) <- genNComposition (n-1)
            f <- fst <$> genSingle
            f' <- fst <$> genSingle
            return ((l >>> f, r >>> f'), lr >>> (f *** f'))

-- This generates two CFSFs: a composition containing id, and one with
-- those id removed.
genNCompsWithId :: Int -> Gen (CFSF ('V Int) ('V Int), CFSF ('V Int) ('V Int))
genNCompsWithId 1 = do
    sing <- fst <$> genSingle
    sing' <- Gen.element [
            sing,
            id >>> sing,
            sing >>> id
        ]
    return (sing, sing')
genNCompsWithId n = do
    (sing, sing') <- genNCompsWithId 1
    (rest, rest') <- genNCompsWithId (n-1)
    return (sing >>> rest, sing' >>> rest)

genNCompsWithPrePairs :: Int ->
    Gen (CFSF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)),
    CFSF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)))
genNCompsWithPrePairs 1 =
    Gen.choice [
        genPrePair,
        dup <$> Gen.constant (arr $ \(Pair (One a) (One b)) -> Pair (One $ a + b) (One b)),
        dup . first . fst <$> genSingle,
        dup . second . fst <$> genSingle
    ]
    where
        dup x = (x,x)
        genPrePair = do
            l <- fst <$> genOneVal
            r <- fst <$> genOneVal
            return (pre (Pair l r), pre l *** pre r)
genNCompsWithPrePairs n = do
    (pair, pair') <- genNCompsWithPrePairs 1
    (rest, rest') <- genNCompsWithPrePairs (n-1)
    return (pair >>> rest, pair' >>> rest')
