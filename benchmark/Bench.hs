{-# LANGUAGE BangPatterns, DataKinds, FlexibleInstances #-}

module Main where

-- RUN WITH
-- stack build loop-compile:bench:bench-vs-yampa

import Criterion
import Criterion.Main
import Hedgehog (Gen)
import Hedgehog.Gen (sample, just)
import Control.DeepSeq
import Data.IORef
import Control.Monad (replicateM_, void)

import FRP.Yampa
import Transform
import ArbitraryProgram
import TestHelpers
import Run
import ArrowCF
import ProgramGen
import Optimise

type TestPair = (CF (V Double) (V Double), SF Double Double)

-- guarantee there's five elements
type TestSet = (TestPair, TestPair, TestPair, TestPair, TestPair)

generateNetworks :: Gen (CF (V Double) (V Double), SF Double Double) -> IO TestSet
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
            (!cf, !sf) <- sample gen
            let !cf' = transform cf
            return (cf', sf)

benchThisGenerator :: String -> Gen (CF (V Double) (V Double), SF Double Double) -> ([Val (V Double)], [Double]) -> Benchmark
benchThisGenerator = undefined
-- benchThisGenerator nam gen (ins, ins') = env (generateNetworks gen) $
--     \ ~((cf1,sf1), (cf2,sf2), (cf3,sf3), (cf4,sf4), (cf5, sf5)) -> bgroup nam [
--         bgroup "net-1" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompCF cf1 ins),
--             bench "sf" $ nf (embed sf1) (deltaEncode 1 ins')
--         ],
--         bgroup "net-2" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompCF cf2 ins),
--             bench "sf" $ nf (embed sf2) (deltaEncode 1 ins')
--         ],
--         bgroup "net-3" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompCF cf3 ins),
--             bench "sf" $ nf (embed sf3) (deltaEncode 1 ins')
--         ],
--         bgroup "net-4" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompCF cf4 ins),
--             bench "sf" $ nf (embed sf4) (deltaEncode 1 ins')
--         ],
--         bgroup "net-5" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompCF cf5 ins),
--             bench "sf" $ nf (embed sf5) (deltaEncode 1 ins')
--         ]
--     ]

generateProgram :: GenParam -> Gen (CF (V Double) (V Double), SF Double Double)
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

benchCF :: CF (V Double) (V Double) -> [Val (V Double)] -> IO ()
benchCF cf ins = do
    inputRef <- newIORef ins
    cfRef <- newIORef cf
    replicateM_ 100000 $ do
        (i : inps) <- readIORef inputRef
        writeIORef inputRef inps
        cf' <- readIORef cfRef
        let (!vb, !cf'') = runCF cf' i
        forceM vb
        writeIORef cfRef cf''

benchSF :: SF Double Double -> [Double] -> IO ()
benchSF sf ins = do
    inputRef <- newIORef ins
    handle <- reactInit (return 0) (\handle' _ v -> forceM v >> return True) sf
    replicateM_ 100000 $ do
        (i : inps) <- readIORef inputRef
        writeIORef inputRef inps
        void $ react handle (1, Just i)

forceM :: (Monad m, NFData a) => a -> m ()
forceM val =
  case rnf val of
    () -> pure ()

main :: IO ()
main = do
    (!ins, !ins') <- sample $ genDoubles 100000 --genInputSamples 100000
    -- defaultMainWith defaultConfig (allGens (ins, ins')) -- NOTE: will likely need to change default config

    -- Let's construct some examples just to make sure.
    (!cf, !sf) <- sample $ generateProgram (GP 50 Nothing) -- makeMassiveNestedLoop 100
    let !cf' = optimiseCF $ transform cf
    !ccf <- compile cf'
    print cf'
    defaultMainWith defaultConfig [
            bench "cf" $ nfIO (benchCF cf' ins),
            bench "sf" $ nfIO (benchSF sf ins')
        ]

instance NFData a => NFData (Val ('V a)) where
    rnf (One a) = rnf a
