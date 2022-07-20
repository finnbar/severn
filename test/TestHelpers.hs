{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}

module TestHelpers where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import ArrowAST
import NF (Val(..), Desc(..))

multiRun :: (arr -> a -> (b, arr)) -> arr -> [a] -> [b]
multiRun _ _ [] = []
multiRun run prog (a : as) =
    let (b, prog') = run prog a
    in b : multiRun run prog' as

arrAST :: (a -> b) -> ArrowAST (V a) (V b)
arrAST f = Arr $ \(One a) -> One (f a)

arrAST2 :: ((a,b) -> (c,d)) -> ArrowAST (P (V a) (V b)) (P (V c) (V d))
arrAST2 f = Arr $ \(Pair (One a) (One b)) -> let (c,d) = f (a,b) in Pair (One c) (One d)

arrAST21 :: (((a,b),c) -> ((d,e),f)) ->
    ArrowAST (P (P (V a) (V b)) (V c)) (P (P (V d) (V e)) (V f))
arrAST21 fn =
    Arr $ \(Pair (Pair (One a) (One b)) (One c)) ->
        let ((d,e),f) = fn ((a,b),c)
        in Pair (Pair (One d) (One e)) (One f)

preAST :: a -> ArrowAST (V a) (V a)
preAST a = Pre (One a)

genOne :: Gen (Val (V Int))
genOne = One <$> Gen.int (Range.linear 0 1000)

genOnes :: Gen [Val (V Int)]
genOnes = Gen.list (Range.linear 5 20) genOne

genPair :: Gen (Val (P (V Int) (V Int)))
genPair = Pair <$> genOne <*> genOne

genPairs :: Gen [Val (P (V Int) (V Int))]
genPairs = Gen.list (Range.linear 5 20) genPair