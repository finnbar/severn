{-# LANGUAGE DataKinds, GADTs, PolyKinds, ScopedTypeVariables,
    StandaloneKindSignatures, FlexibleInstances #-}

module ArrowNFGen where

import Prelude hiding (id)

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Kind (Constraint)
import Data.Proxy (Proxy(..))

import ArrowNF
import TestHelpers

genDistributiveTest :: Int ->
    Gen (ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)),
        ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)))
genDistributiveTest n
    | n <= 0 = undefined
    | otherwise = do
        ((l,r),lr) <- genNComposition n
        return (l *** r, lr)
    where
        -- LHS of tuple = (l, r) to eventually be l *** r
        -- RHS of tuple = lr which is each (l *** r) composed
        genNComposition :: Int ->
            Gen ((ANF ('V Int) ('V Int), ANF ('V Int) ('V Int)),
                ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)))
        genNComposition 1 = do
            f <- fst <$> genSingle
            f' <- fst <$> genSingle
            return ((f, f'), f *** f')
        genNComposition n = do
            ((l, r),lr) <- genNComposition (n-1)
            f <- fst <$> genSingle
            f' <- fst <$> genSingle
            return ((l >>> f, r >>> f'), lr >>> (f *** f'))

genNCompsWithId :: Int -> Gen (ANF ('V Int) ('V Int), ANF ('V Int) ('V Int))
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

genNCompsWithPairId :: Int ->
    Gen (ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)),
    ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)))
genNCompsWithPairId 1 = do
    pair <- fst <$> genPair
    pair' <- Gen.element [
            pair,
            (id *** id) >>> pair,
            pair >>> (id *** id),
            pair >>> id,
            id >>> pair
        ]
    return (pair, pair')
genNCompsWithPairId n = do
    (pair, pair') <- genNCompsWithPairId 1
    (rest, rest') <- genNCompsWithPairId (n-1)
    return (pair >>> rest, pair' >>> rest')

genNCompsWithPrePairs :: Int ->
    Gen (ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)),
    ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)))
genNCompsWithPrePairs 1 =
    Gen.choice [
        dup <$> Gen.constant (arr $ \(Pair (One a) (One b)) -> Pair (One $ a + b) (One b)),
        genPrePair,
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

type GenCrunchTrees :: forall s. Desc s -> Constraint
class GenCrunchTrees a where
    genCrunchTrees :: Proxy a ->
        Gen ((ANF a a, ANF a a), -- left and right arguments to compose
            (ANF a a, ANF a a)) -- those arguments after crunching

instance GenCrunchTrees ('V Int) where
    genCrunchTrees _ = Gen.choice [
            do
                lhs <- fst <$> genSingle
                return ((lhs, id), (id, lhs)),
            do
                rhs <- fst <$> genSingle
                return ((id, rhs), (id, rhs))
        ]

instance forall a b. (GenCrunchTrees a, GenCrunchTrees b)
    => GenCrunchTrees ('P a b) where
    genCrunchTrees _ = do
        ((lt, rt), (lt', rt')) <- genCrunchTrees (Proxy :: Proxy a)
        ((lb, rb), (lb', rb')) <- genCrunchTrees (Proxy :: Proxy b)
        return ((lt *** lb, rt *** rb), (lt' *** lb', rt' *** rb'))
