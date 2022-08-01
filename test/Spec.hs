{-# LANGUAGE BangPatterns #-}

import Hedgehog

import ArrowNFSpec
import TransformSpec

import System.Exit (exitFailure)
import Control.Monad

main :: IO ()
main = do
    !res <- mapM checkSequential [arrowNFSpec, transformSpec]
    unless (and res) exitFailure