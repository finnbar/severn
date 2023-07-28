{-# LANGUAGE BangPatterns, DataKinds, FlexibleInstances #-}

module Main where

-- RUN WITH
-- stack build loop-compile:bench:bench-vs-yampa

import Criterion
import Criterion.Main
import Hedgehog (Gen)
import Hedgehog.Gen (sample, just)
import Control.DeepSeq

import FRP.Yampa
import Transform
import ArbitraryProgram
import TestHelpers
import Run
import NF
import ProgramGen

type TestPair = (ANF (V Double) (V Double), SF Double Double)

-- guarantee there's five elements
type TestSet = (TestPair, TestPair, TestPair, TestPair, TestPair)

generateNetworks :: Gen (ANF (V Double) (V Double), SF Double Double) -> IO TestSet
generateNetworks gen = do
    !a <- makeOne
    !b <- makeOne
    !c <- makeOne
    !d <- makeOne
    !e <- makeOne
    return (a,b,c,d,e)
    where
        makeOne :: IO TestPair
        makeOne = do
            (!anf, !sf) <- sample gen
            let !anf' = transform anf
            return (anf', sf)

benchThisGenerator :: String -> Gen (ANF (V Double) (V Double), SF Double Double) -> ([Val (V Double)], [Double]) -> Benchmark
benchThisGenerator = undefined
-- benchThisGenerator nam gen (ins, ins') = env (generateNetworks gen) $
--     \ ~((anf1,sf1), (anf2,sf2), (anf3,sf3), (anf4,sf4), (anf5, sf5)) -> bgroup nam [
--         bgroup "net-1" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompANF anf1 ins),
--             bench "sf" $ nf (embed sf1) (deltaEncode 1 ins')
--         ],
--         bgroup "net-2" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompANF anf2 ins),
--             bench "sf" $ nf (embed sf2) (deltaEncode 1 ins')
--         ],
--         bgroup "net-3" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompANF anf3 ins),
--             bench "sf" $ nf (embed sf3) (deltaEncode 1 ins')
--         ],
--         bgroup "net-4" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompANF anf4 ins),
--             bench "sf" $ nf (embed sf4) (deltaEncode 1 ins')
--         ],
--         bgroup "net-5" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompANF anf5 ins),
--             bench "sf" $ nf (embed sf5) (deltaEncode 1 ins')
--         ]
--     ]

generateProgram :: GenParam -> Gen (ANF (V Double) (V Double), SF Double Double)
generateProgram gp = just $ genProg ProxV ProxV gp

allGens :: ([Val (V Double)], [Double]) -> [Benchmark]
allGens inputs = concat $ flip map [25,50,100,150,200,250,300] $
    \size -> [
            benchThisGenerator "no-loop" (generateProgram (GP size (Just []))) inputs,
            benchThisGenerator "one-loop" (generateProgram (GP size (Just [1]))) inputs,
            benchThisGenerator "deep-loops" (generateProgram (GP size (Just $ sizeToDeep size))) inputs,
            benchThisGenerator "shallow-loops" (generateProgram (GP size (Just $ sizeToShallow size))) inputs,
            benchThisGenerator "branching-loops" (generateProgram (GP size (Just $ sizeToBranching size))) inputs,
            benchThisGenerator "any-loops" (generateProgram (GP size Nothing)) inputs
        ]
    where
        sizeToDeep :: Int -> [Int]
        sizeToDeep n = replicate (n `div` 10) 1
        sizeToShallow :: Int -> [Int]
        sizeToShallow n = [n `div` 10]
        sizeToBranching :: Int -> [Int]
        sizeToBranching n = replicate (floor $ logBase 2.0 (fromIntegral n / 10)) 2

-- TODO: We're getting some very weird performance results.
-- I think the writing of IORefs at the start is slowing SFRP down vs ANF and SF.
-- See what Chupin's impl does (his ExecutionMachine is like CompiledANF).
-- Also important to note that our noLoop tests consist of solely Arr, which means that I think Yampa can optimise heavily.
-- (The SFRP tests done by Chupin include integrals, which are naturally stateful.)
-- So plan:
-- 1. Allow _some_ pre in our network, to avoid ridiculous optimisation by Yampa. DONE
-- 2. Add some IORef stuff to ANF and SF's benchmarks.
-- 3. See what happens.

main :: IO ()
main = do
    (!ins, !ins') <- sample $ genDoubles 100000 --genInputSamples 100000
    -- defaultMainWith defaultConfig (allGens (ins, ins')) -- NOTE: will likely need to change default config

    -- Let's construct some examples just to make sure.
    (!anf, !sf) <- sample $ generateProgram (GP 25 (Just [1])) -- makeMassiveNestedLoop 100
    let !anf' = transform anf
    !canf <- compile anf'
    print anf
    print anf'
    defaultMainWith defaultConfig $ [
            bench "anf" $ nf (multiRun runANF anf') ins,
            bench "sf" $ nf (embed sf) (deltaEncode 1 ins')
        ]

instance NFData a => NFData (Val ('V a)) where
    rnf (One a) = rnf a
