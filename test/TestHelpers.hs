{-# LANGUAGE DataKinds, GADTs, MultiParamTypeClasses,
    ExplicitForAll, PolyKinds, FlexibleInstances #-}

module TestHelpers where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import ArrowNF

multiRun :: (arr -> a -> (b, arr)) -> arr -> [a] -> [b]
multiRun _ _ [] = []
multiRun run prog (a : as) =
    let (b, prog') = run prog a
    in b : multiRun run prog' as

genOneVal :: Gen (Val (V Int))
genOneVal = One <$> Gen.int (Range.linear 0 1000)

genOneVals :: Gen [Val (V Int)]
genOneVals = Gen.list (Range.linear 5 20) genOneVal

genPairVal :: Gen (Val (P (V Int) (V Int)))
genPairVal = Pair <$> genOneVal <*> genOneVal

genPairVals :: Gen [Val (P (V Int) (V Int))]
genPairVals = Gen.list (Range.linear 5 20) genPairVal

genSingle :: Gen (ANF ('V Int) ('V Int))
genSingle = Gen.choice [
        Gen.constant (arr $ \(One a) -> One $ a+1),
        pre <$> genOneVal
    ]

genPair :: Gen (ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)))
genPair = Gen.choice [
        Gen.constant (arr $ \(Pair (One a) (One b)) -> Pair (One $ a + b) (One b)),
        (***) <$> genSingle <*> genSingle,
        first <$> genSingle,
        second <$> genSingle
    ]

genTrio :: 
    Gen (ANF ('P ('P ('V Int) ('V Int)) ('V Int)) ('P ('P ('V Int) ('V Int)) ('V Int)))
genTrio = Gen.choice [
        (***) <$> genPair <*> genSingle,
        Gen.constant (WithoutLoop (lift_ Juggle)),
        Gen.constant (arr
            (\(Pair (Pair (One a) (One b)) (One c)) ->
                Pair (Pair (One b) (One c)) (One a)))
    ]

genSingleProg :: Int -> Gen (ANF ('V Int) ('V Int))
genSingleProg 1 = genSingle
genSingleProg n = (>>>) <$> genSingle <*> genSingleProg (n-1)

genPairProg :: Int -> Gen (ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)))
genPairProg 1 = genPair
genPairProg n = (>>>) <$> genPair <*> genPairProg (n-1)

genTrioProg :: Int ->
    Gen (ANF ('P ('P ('V Int) ('V Int)) ('V Int)) ('P ('P ('V Int) ('V Int)) ('V Int)))
genTrioProg 1 = genTrio
genTrioProg n = (>>>) <$> genTrio <*> genTrioProg (n-1)
