{-# LANGUAGE BangPatterns, DataKinds, FlexibleInstances, GADTs #-}

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

-- (((Arr >>> Pre) >>> Arr) >>> ... Arr)
generateBadBracketing :: Int -> (CFSF (V Double) (V Double), SF Double Double)
generateBadBracketing n = gbb n (compPair (arbitraryFn ProxV ProxV) (genPre ProxV))
    where
        gbb :: Int -> (CFSF (V Double) (V Double), SF Double Double) -> (CFSF (V Double) (V Double), SF Double Double)
        gbb 0 prog = prog
        gbb n prog = gbb (n-1) (compPair prog (arbitraryFn ProxV ProxV))

-- (Arr >>> (Pre ... >>> (Arr >>> (Arr >>> Arr))))
generateGoodBracketing :: Int -> (CFSF (V Double) (V Double), SF Double Double)
generateGoodBracketing n = compPair (compPair (arbitraryFn ProxV ProxV) (genPre ProxV)) $ ggb n
    where
        ggb :: Int -> (CFSF (V Double) (V Double), SF Double Double)
        ggb 1 = arbitraryFn ProxV ProxV
        ggb n = compPair (arbitraryFn ProxV ProxV) $ ggb (n-1)

main :: IO ()
main =
    do
        !inputs <- sample $ genDoubles 100000
        bad <- benchThisGenerator "bad bracketing" (return $ generateBadBracketing 300) inputs
        good <- benchThisGenerator "good bracketing" (return $ generateGoodBracketing 300) inputs
        arronly0 <- benchThisGenerator "arr0 micro" (return (Single $ Arr Prelude.id, FRP.Yampa.arr Prelude.id)) inputs
        arronly <- benchThisGenerator "arr micro" (return $ arbitraryFn ProxV ProxV) inputs
        arronly2 <- benchThisGenerator "arr2 micro" (return $ compPair (arbitraryFn ProxV ProxV) (arbitraryFn ProxV ProxV)) inputs
        preonly <- benchThisGenerator "pre micro" (return $ genPre ProxV) inputs
        let !benches = [bad, good{-, arronly0, arronly, arronly2, preonly-}]
        defaultMainWith defaultConfig benches

-- CURRENT TIMING OF ABOVE
-- bad/sfrp 3.583s
-- bad/cfsf 1.688s
-- bad/sf   1.026s
-- good/sfrp 1.341s
-- good/cfsf 1.311s
-- good/sf   815.1ms
-- arr/sfrp 26.93ms
-- arr/cfsf 16.74ms
-- arr/sf   24.00ms
-- pre/sfrp 24.95ms
-- pre/cfsf 15.18ms
-- pre/sf   24.11ms
-- run on my laptop
-- Yampa likely wins for the larger programs because the programs are equivalent to Arr >>> Pre,
-- and Yampa seems to keep winning on tiny programs - why? What startup cost do we have that Yampa doesn't?
-- TODO Check the benchmarking programs themselves to make sure there's no weirdness there.
-- I think it might be the cost of routing that's causing issues here?
-- Also, I'm guessing that cfsf wins arr because strict vs lazy?
-- and possibly the same for pre?
-- Yampa's SFCpAXA constructor might be throwing weirdness into the mix. Especially as it reduces the number
-- of allocations of e.g. Arr >>> Pre >>> Arr.
-- If we wanted to make a really performant library we could implement similar combinators to avoid the performance cost,
-- e.g. CL :: (pure SF) -> (effectful SF) -> (effectful SF)
-- and then by not providing one which takes two pure SFs, force the arrow laws to apply by construction.

allTests :: IO ()
allTests =
    do
        cPSL "Running"
        !inputs <- sample $ genDoubles 100000 --genInputSamples 100000
        let sizes = [25,50,100,150,200,250,300]
        cPSL "Generating loopProportion=0"
        noLoop <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0)) inputs
        cPSL "Generating loopProportion=0.1"
        loop10 <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0.1)) inputs
        cPSL "Generating loopProportion=0.25"
        loop25 <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0.25)) inputs
        cPSL "Generating loopProportion=0.5"
        loop50 <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0.5)) inputs
        cPSL "Done generating"
        let !benches = [bgroup "lp=0" noLoop, bgroup "lp=0.1" loop10, bgroup "lp=0.25" loop25, bgroup "lp=0.5" loop50]
        defaultMainWith defaultConfig benches -- NOTE: will likely need to change default config

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

