{-# LANGUAGE DataKinds, BangPatterns, TemplateHaskell,
    StandaloneDeriving, DeriveLift, ScopedTypeVariables,
    FlexibleInstances, NumericUnderscores, GADTs #-}

module TestPrograms where

import ProgGenTH
import CFSF
import SFRP
import PreIO
import Transform
import Optimise (optimiseCFSF)
import TestHelpers (Simplify)
import BenchHelpers

import FRP.Yampa
import Criterion
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

deriving instance Lift (Val (V Double))

benchmarkSet :: String ->
    (SF Double Double, CFSF (V Double) (V Double)) ->
    ([Val (V Double)], [Double]) -> IO Benchmark
benchmarkSet nam (!sf, cfsf) (ins, ins') = do
    let !optcfsf = optimiseCFSF $ transform cfsf
    !preIO <- compilePreIO optcfsf
    !allIO <- compile optcfsf
    return $ bgroup nam [
            bench "allIO" $ whnfAppIO (benchCompCFSF allIO) ins,
            bench "preIO" $ whnfAppIO (benchCompCFSF preIO) ins,
            bench "sf-strict" $ whnfAppIO (benchCFSF optcfsf) ins,
            bench "sf" $ whnfAppIO (benchSF sf) ins'
        ]

ins' :: [Double]
ins' = [1..100_000]
ins :: [Val (V Double)]
ins = map One ins'

toList :: Quote m => [Code m a] -> Code m [a]
toList [] = [|| [] ||]
toList (x : xs) = let l = toList xs in [|| $$x : $$l ||]

buildBenchmark :: forall m. Quote m =>
    (Int -> (Code m (SF Double Double), Code m (CFSF (V Double) (V Double)))) ->
    [Int] -> String ->
    Code m (IO Benchmark)
buildBenchmark progsplice sizes nam =
    [|| sequence $$(toList $ map buildsizerun sizes) >>= return . bgroup nam ||]
    where
        buildsizerun :: Quote m => Int -> Code m (IO Benchmark)
        buildsizerun size = [|| benchmarkSet (show size) $$(make $ progsplice size) (ins, ins') ||]