{-# LANGUAGE DataKinds, BangPatterns, TemplateHaskell,
    StandaloneDeriving, DeriveLift, ScopedTypeVariables,
    FlexibleInstances, NumericUnderscores, GADTs #-}

module TestPrograms where

import ProgGenTH
import CFSF
import Transform
import Optimise (optimiseCFSF)
import TestHelpers (Simplify)
import BenchHelpers

import FRP.Yampa
import Criterion
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

deriving instance Lift (Val (V Double))

ins' :: [Double]
ins' = [1..100_000]
ins :: [Val (V Double)]
ins = map One ins'

toList :: Quote m => [Code m a] -> Code m [a]
toList [] = [|| [] ||]
toList (x : xs) = let l = toList xs in [|| $$x : $$l ||]

buildBenchmark :: forall m. Quote m =>
    (Int -> (Code m (CFSF (V Double) (V Double)), Code m (SF Double Double))) ->
    [Int] -> String ->
    Code m (IO Benchmark)
buildBenchmark progsplice sizes nam =
    [|| sequence $$(toList $ map buildsizerun sizes) >>= return . bgroup nam ||]
    where
        buildsizerun :: Quote m => Int -> Code m (IO Benchmark)
        buildsizerun size = [|| benchTheseNetworks (show size) $$(make $ progsplice size) (ins, ins') ||]