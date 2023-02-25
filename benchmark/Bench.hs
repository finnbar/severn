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
import Control.Monad (replicateM_, void, forM)
import System.IO (Handle, hFlush, stderr, stdout, hPutStr)

import FRP.Yampa
import Transform
import ArbitraryProgram
import TestHelpers
import Run
import ArrowCFSF
import Optimise

type TestPair = (CFSF (V Double) (V Double), SF Double Double)

generateNetworks :: Gen (CFSF (V Double) (V Double), SF Double Double) -> IO TestPair
generateNetworks gen = do
    (!cfsf, !sf) <- sample gen
    let !cfsf' = optimiseCFSF $ transform cfsf
    return (cfsf', sf)

benchThisGenerator :: String -> Gen (CFSF (V Double) (V Double), SF Double Double) -> ([Val (V Double)], [Double]) -> IO Benchmark
benchThisGenerator nam gen (ins, ins') = do
    (!ccfsf1,!cfsf1,!sf1) <- generateNetworks gen
    cPSL $ "Generated benchmarks for " ++ nam
    return $ bgroup nam [
            bench "cfsf" $ whnfAppIO (benchCFSF cfsf1) ins,
            bench "sf" $ whnfAppIO (benchSF sf1) ins'
        ]

generateProgram :: GenParam -> Gen (CFSF (V Double) (V Double), SF Double Double)
generateProgram gp = just $ genProg ProxV ProxV gp

cPSL :: String -> IO ()
cPSL s = putStrLn s >> hFlush stdout

cP :: Show a => a -> IO ()
cP = cPSL . show

main :: IO ()
main =
    do
        cPSL "Running"
        !inputs <- sample $ genDoubles 100000 --genInputSamples 100000
        let sizes = [100]--[25,50,100,150,200,250,300]
        cPSL "Generating noLoop"
        noLoop <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (GP size (Just []))) inputs
        cPSL "Generating deepLoop"
        deepLoop <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (GP size (Just $ sizeToDeep size))) inputs
        cPSL "Generating shallowLoop"
        shallowLoop <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (GP size (Just $ sizeToShallow size))) inputs
        cPSL "Generating mixedLoop"
        mixedLoop <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (GP size (Just $ sizeToBranching size))) inputs
        cPSL "Done generating"
        let !benches = [bgroup "no-loop" noLoop, bgroup "deep-loop" deepLoop, bgroup "shallow-loop" shallowLoop, bgroup "mixed-loop" mixedLoop]
        defaultMainWith defaultConfig benches -- NOTE: will likely need to change default config
    where
        fraction :: Num a => a
        fraction = 5
        sizeToDeep :: Int -> [Int]
        sizeToDeep n = replicate (n `div` fraction) 1
        sizeToShallow :: Int -> [Int]
        sizeToShallow n = [n `div` fraction]
        sizeToBranching :: Int -> [Int]
        sizeToBranching n = replicate (floor $ logBase 2.0 (fromIntegral n / fraction)) 2


    -- -- Let's construct some examples just to make sure.
    -- (!cfsf, !sf) <- sample $ generateProgram (GP 50 (Just [2,2,2])) -- makeMassiveNestedLoop 100
    -- let !cfsf' = optimiseCFSF $ transform cfsf
    -- !ccfsf <- compile cfsf'
    -- print cfsf'
    -- defaultMainWith defaultConfig [
    --         bench "cfsf" $ whnfIO $ benchCFSF cfsf' ins,
    --         bench "sf" $ whnfIO $ benchSF sf ins'
    --     ]

instance NFData a => NFData (Val ('V a)) where
    rnf (One a) = rnf a

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
        b <- react handle (1, Just i)
        forceM b

forceM :: (Monad m, NFData a) => a -> m ()
forceM val =
  case rnf val of
    () -> pure ()

