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
import ArrowCFSF
import Optimise

type TestPair = (CFSF (V Double) (V Double), SF Double Double)

-- guarantee there's five elements
type TestSet = (TestPair, TestPair, TestPair, TestPair, TestPair)

generateNetworks :: Gen (CFSF (V Double) (V Double), SF Double Double) -> IO TestSet
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
            (!cfsf, !sf) <- sample gen
            let !cfsf' = transform cfsf
            return (cfsf', sf)

benchThisGenerator :: String -> Gen (CFSF (V Double) (V Double), SF Double Double) -> ([Val (V Double)], [Double]) -> Benchmark
benchThisGenerator = undefined
-- benchThisGenerator nam gen (ins, ins') = env (generateNetworks gen) $
--     \ ~((cfsf1,sf1), (cfsf2,sf2), (cfsf3,sf3), (cfsf4,sf4), (cfsf5, sf5)) -> bgroup nam [
--         bgroup "net-1" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompCFSF cfsf1 ins),
--             bench "sf" $ nf (embed sf1) (deltaEncode 1 ins')
--         ],
--         bgroup "net-2" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompCFSF cfsf2 ins),
--             bench "sf" $ nf (embed sf2) (deltaEncode 1 ins')
--         ],
--         bgroup "net-3" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompCFSF cfsf3 ins),
--             bench "sf" $ nf (embed sf3) (deltaEncode 1 ins')
--         ],
--         bgroup "net-4" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompCFSF cfsf4 ins),
--             bench "sf" $ nf (embed sf4) (deltaEncode 1 ins')
--         ],
--         bgroup "net-5" [
--             bench "sfrp" $ nfIO (map simplify <$> runCompCFSF cfsf5 ins),
--             bench "sf" $ nf (embed sf5) (deltaEncode 1 ins')
--         ]
--     ]

generateProgram :: GenParam -> Gen (CFSF (V Double) (V Double), SF Double Double)
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

benchCFSF :: CFSF (V Double) (V Double) -> [Val (V Double)] -> IO ()
benchCFSF cfsf ins = do
    inputRef <- newIORef ins
    cfsfRef <- newIORef cfsf
    replicateM_ 100000 $ do
        (i : inps) <- readIORef inputRef
        writeIORef inputRef inps
        cfsf' <- readIORef cfsfRef
        let (!vb, !cfsf'') = runCFSF cfsf' i
        forceM vb
        writeIORef cfsfRef cfsf''

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
    (!cfsf, !sf) <- sample $ generateProgram (GP 50 Nothing) -- makeMassiveNestedLoop 100
    let !cfsf' = optimiseCFSF $ transform cfsf
    !ccfsf <- compile cfsf'
    print cfsf'
    defaultMainWith defaultConfig [
            bench "cfsf" $ nfIO (benchCFSF cfsf' ins),
            bench "sf" $ nfIO (benchSF sf ins')
        ]

instance NFData a => NFData (Val ('V a)) where
    rnf (One a) = rnf a
