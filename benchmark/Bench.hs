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
import Run (runCFSF)
import ArrowCFSF
import Optimise

data TestSet = TS {
    cfsf :: CFSF (V Double) (V Double),
    sf :: SF Double Double
}

generateNetworks :: Gen (CFSF (V Double) (V Double), SF Double Double) -> IO TestSet
generateNetworks gen = do
    (!cfsf, !sf) <- sample gen
    let !cfsf' = optimiseCFSF $ transform cfsf
    return $ TS cfsf' sf

-- TODO: make sure ccfsf etc are _fully_ evaluated (not WHNF but NF), likely via NFData instances.
-- (Note that SFRP tests use rnf with some... somewhat lawful instances. This is likely what we need to do too.)
-- ! only goes to WHNF, hence why I think SFRP doesn't really use it.
-- Then make sure whnfAppIO is correct for our tests, rather than similar functions
benchThisGenerator :: String -> Gen (CFSF (V Double) (V Double), SF Double Double) -> ([Val (V Double)], [Double]) -> IO Benchmark
benchThisGenerator nam gen (ins, ins') = do
    TS !cfsf !sf <- generateNetworks gen
    cPSL $ "Generated benchmarks for " ++ nam
    return $ bgroup nam [
            bench "cfsf" $ whnfAppIO (benchCFSF cfsf) ins,
            bench "sf" $ whnfAppIO (benchSF sf) ins'
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
main = allTests

yampatest = do
    let sf = snd $ generateGoodBracketing 200
    (_,!inp100) <- sample $ genDoubles 1000
    (_,!inp1000) <- sample $ genDoubles 10000
    (_,!inp10000) <- sample $ genDoubles 100000
    let bnch = [
            bench "sf100" $ nfAppIO (benchSF sf) inp100,
            bench "sf1000" $ nfAppIO (benchSF sf) inp1000,
            bench "sf10000" $ nfAppIO (benchSF sf) inp10000]
    defaultMainWith defaultConfig bnch


specialCases :: IO ()
specialCases =
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

-- TODO Check the benchmarking programs themselves to make sure there's no weirdness there.
-- I think it might be the cost of routing that's causing issues here?
-- Also, I'm guessing that cfsf wins arr because strict vs lazy?
-- and possibly the same for pre?
-- Yampa's SFCpAXA constructor might be throwing weirdness into the mix. Especially as it reduces the number
-- of allocations of e.g. Arr >>> Pre >>> Arr.
-- If we wanted to make a really performant library we could implement similar combinators to avoid the performance cost,
-- e.g. CL :: (pure SF) -> (effectful SF) -> (effectful SF)
-- and then by not providing one which takes two pure SFs, force the arrow laws to apply by construction.
-- TODO: Heap profile. Then look at rnf in Chupin's SFRP and compare to ours.

allTests :: IO ()
allTests =
    do
        cPSL "Running"
        !inputs <- sample $ genDoubles 100000 --genInputSamples 100000
        let sizes = [{-25,50,100,-}150{-,200,250,300-}]
        cPSL "Generating loopProportion=0"
        noLoop <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0)) inputs
        cPSL "Generating loopProportion=0.1"
        loop10 <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0.1)) inputs
        cPSL "Generating loopProportion=0.25"
        loop25 <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0.25)) inputs
        cPSL "Generating loopProportion=0.5"
        loop50 <- forM sizes $ \size -> benchThisGenerator (show size) (generateProgram (makeGenParam size 0.5)) inputs
        cPSL "Done generating"
        let !benches = [{-bgroup "lp=0" noLoop, -}bgroup "lp=0.1" loop10, bgroup "lp=0.25" loop25, bgroup "lp=0.5" loop50]
        defaultMainWith defaultConfig benches -- NOTE: will likely need to change default config

instance NFData a => NFData (Val ('V a)) where
    rnf (One a) = rnf a

benchCFSF :: CFSF (V Double) (V Double) -> [Val (V Double)] -> IO ()
benchCFSF cfsf ins = do
    inputRef <- newIORef ins
    cfsfRef <- newIORef cfsf
    replicateM_ (length ins) $ do
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
    replicateM_ (length ins) $ do
        (i : inps) <- readIORef inputRef
        writeIORef inputRef inps
        b <- react handle (1, Just i)
        forceM b

forceM :: (Monad m, NFData a) => a -> m ()
forceM val =
  case rnf val of
    () -> pure ()

