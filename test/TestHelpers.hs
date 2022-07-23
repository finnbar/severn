{-# LANGUAGE DataKinds, GADTs, MultiParamTypeClasses,
    ExplicitForAll, PolyKinds, FlexibleInstances #-}

module TestHelpers where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import ArrowNF
import qualified Control.Arrow as A
import FRP.Yampa (SF, iPre)

multiRun :: (arr -> a -> (b, arr)) -> arr -> [a] -> [b]
multiRun _ _ [] = []
multiRun run prog (a : as) =
    let (b, prog') = run prog a
    in b : multiRun run prog' as

-- IMPORTANT NOTE
-- All of the generators generate an ArrowNF program and its equivalent Yampa program.
-- In ArrowNFSpec, we just use the first output via `fst <$>`.
-- In TransformSpec, we check for equivalence so use both.

splitGen :: (a -> b, a -> c) -> Gen a -> Gen (b, c)
splitGen (f,g) gen = gen >>= \x -> return (f x, g x)

bimapGen :: (a -> b) -> (c -> d) -> Gen (a,c) -> Gen (b,d)
bimapGen f g gen = do
    (a,c) <- gen
    return (f a, g c)

bimapTwoGen :: (a -> b -> c) -> (d -> e -> f) -> Gen (a,d) -> Gen (b,e) -> Gen (c, f)
bimapTwoGen f g gen1 gen2 = do
    (a,d) <- gen1
    (b,e) <- gen2
    return (f a b, g d e)

genOneVal :: Gen (Val (V Int), Int)
genOneVal = (One, Prelude.id) `splitGen` Gen.int (Range.linear 0 1000)

genOneVals :: Gen ([Val (V Int)], [Int])
genOneVals = unzip <$> Gen.list (Range.linear 5 20) genOneVal

genPairVal :: Gen (Val (P (V Int) (V Int)), (Int, Int))
genPairVal = bimapTwoGen Pair (,) genOneVal genOneVal

genPairVals :: Gen ([Val (P (V Int) (V Int))], [(Int, Int)])
genPairVals = unzip <$> Gen.list (Range.linear 5 20) genPairVal

genSingle :: Gen (ANF ('V Int) ('V Int), SF Int Int)
genSingle = Gen.choice [
        Gen.constant (arr $ \(One a) -> One $ a+1, A.arr (+1)),
        bimapGen pre iPre genOneVal
    ]

genPair :: Gen (ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)), SF (Int, Int) (Int, Int))
genPair = Gen.choice [
        Gen.constant (arr $ \(Pair (One a) (One b)) -> Pair (One $ a + b) (One a), A.arr (\(x,y) -> (x+y, x))),
        bimapTwoGen (***) (A.***) genSingle genSingle,
        bimapGen first A.first genSingle,
        bimapGen second A.second genSingle
    ]

genTrio :: 
    Gen (ANF ('P ('P ('V Int) ('V Int)) ('V Int)) ('P ('P ('V Int) ('V Int)) ('V Int)),
        SF ((Int, Int), Int) ((Int, Int), Int))
genTrio = Gen.choice [
        bimapTwoGen (***) (A.***) genPair genSingle,
        Gen.constant (WithoutLoop (lift_ Juggle), A.arr (\(~(~(a,b),c)) -> ((a,c),b))),
        Gen.constant (arr
            (\(Pair (Pair (One a) (One b)) (One c)) ->
                Pair (Pair (One b) (One c)) (One a)),
            A.arr $ \(~(~(a,b),c)) -> ((b,c),a))
    ]

genSingleProg :: Int -> Gen (ANF ('V Int) ('V Int), SF Int Int)
genSingleProg 1 = genSingle
genSingleProg n = bimapTwoGen (>>>) (A.>>>) genSingle $ genSingleProg (n-1)

genPairProg :: Int -> Gen (ANF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)), SF (Int, Int) (Int, Int))
genPairProg 1 = genPair
genPairProg n = bimapTwoGen (>>>) (A.>>>) genPair $ genPairProg (n-1)

genTrioProg :: Int ->
    Gen (ANF ('P ('P ('V Int) ('V Int)) ('V Int)) ('P ('P ('V Int) ('V Int)) ('V Int)),
        SF ((Int, Int), Int) ((Int, Int), Int))
genTrioProg 1 = genTrio
genTrioProg n = bimapTwoGen (>>>) (A.>>>) genTrio $ genTrioProg (n-1)
