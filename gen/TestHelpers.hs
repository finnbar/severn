{-# LANGUAGE DataKinds, GADTs, MultiParamTypeClasses,
    ExplicitForAll, PolyKinds, FlexibleInstances, TypeFamilies, StandaloneKindSignatures #-}

module TestHelpers where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import ArrowCF
import qualified Control.Arrow as A
import FRP.Yampa (SF, iPre)

type Simplify :: forall s. Desc s -> *
type family Simplify x where
    Simplify (V a) = a
    Simplify (P a b) = (Simplify a, Simplify b)

multiRun :: (arr -> a -> (b, arr)) -> arr -> [a] -> [b]
multiRun _ _ [] = []
multiRun run prog (a : as) =
    let (b, prog') = run prog a
    in b : multiRun run prog' as

-- IMPORTANT NOTE
-- All of the generators generate a CF program and its equivalent Yampa program.
-- In ArrowCFSpec, we just use the first output via `fst <$>`.
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

genSingle :: Gen (CF ('V Int) ('V Int), SF Int Int)
genSingle = Gen.choice [
        Gen.constant (arr $ \(One a) -> One $ a+1, A.arr (+1)),
        bimapGen pre iPre genOneVal
    ]

genPair :: Gen (CF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)), SF (Int, Int) (Int, Int))
genPair = Gen.choice [
        Gen.constant (arr $ \(Pair (One a) (One b)) -> Pair (One $ a + b) (One a), A.arr (\(x,y) -> (x+y, x))),
        bimapTwoGen (***) (A.***) genSingle genSingle,
        bimapGen first A.first genSingle,
        bimapGen second A.second genSingle
    ]

genTrio :: 
    Gen (CF ('P ('P ('V Int) ('V Int)) ('V Int)) ('P ('P ('V Int) ('V Int)) ('V Int)),
        SF ((Int, Int), Int) ((Int, Int), Int))
genTrio = Gen.choice [
        bimapTwoGen (***) (A.***) genPair genSingle,
        Gen.constant (arr
            (\(Pair (Pair (One a) (One b)) (One c)) ->
                Pair (Pair (One b) (One c)) (One a)),
            A.arr $ \(~(~(a,b),c)) -> ((b,c),a))
    ]

genSingleProg :: Int -> Gen (CF ('V Int) ('V Int), SF Int Int)
genSingleProg 1 = genSingle
genSingleProg n = bimapTwoGen (>>>) (A.>>>) genSingle $ genSingleProg (n-1)

genPairProg :: Int -> Gen (CF ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int)), SF (Int, Int) (Int, Int))
genPairProg 1 = genPair
genPairProg n = bimapTwoGen (>>>) (A.>>>) genPair $ genPairProg (n-1)

genTrioProg :: Int ->
    Gen (CF ('P ('P ('V Int) ('V Int)) ('V Int)) ('P ('P ('V Int) ('V Int)) ('V Int)),
        SF ((Int, Int), Int) ((Int, Int), Int))
genTrioProg 1 = genTrio
genTrioProg n = bimapTwoGen (>>>) (A.>>>) genTrio $ genTrioProg (n-1)

-- Gen some composition which can be crushed into a pre.
genCrushable :: Gen (CF (P (V Int) (V Int)) (P (V Int) (V Int)), SF (Int, Int) (Int, Int))
genCrushable =
    do
        (a,a') <- genSingle
        (i,i') <- genOneVal
        (j,j') <- genOneVal
        Gen.element [
            -- (a *** pre j) >>> (pre i *** id)
            ((a *** pre j) >>> first (pre i), (a' A.*** iPre j') A.>>> A.first (iPre i')),
            -- (pre i *** a) >>> (id *** pre j)
            ((pre i *** a) >>> second (pre j), (iPre i' A.*** a') A.>>> A.second (iPre j')),
            -- first (pre i) >>> second (pre j)
            (first (pre i) >>> second (pre j), A.first (iPre i') A.>>> A.second (iPre j')),
            -- second (pre j) >>> first (pre i)
            (second (pre j) >>> first (pre i), A.second (iPre j') A.>>> A.first (iPre i')) ]

chooseAndTry :: [Gen (Maybe a)] -> Gen (Maybe a)
chooseAndTry gens = Gen.shuffle gens >>= tryAll
    where
        tryAll :: [Gen (Maybe a)] -> Gen (Maybe a)
        tryAll [] = return Nothing
        tryAll (x : xs) = do
            vx <- x
            case vx of
                Just res -> return (Just res)
                Nothing -> tryAll xs

maybeMap :: Monad m => (a -> b -> c) -> m (Maybe a) -> m (Maybe b) -> m (Maybe c)
maybeMap f lg rg = do
    left <- lg
    right <- rg
    return $ f <$> left <*> right

genDoubles :: Int -> Gen ([Val (V Double)], [Double])
genDoubles i = unzip <$> Gen.list (Range.singleton i) genDouble
    where
        genDouble = do
            d <- Gen.double (Range.linearFrac 0 100)
            return (One d, d)