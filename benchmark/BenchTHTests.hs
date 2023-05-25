{-# LANGUAGE TemplateHaskell, GADTs #-}

module BenchTHTests where

import TestPrograms
import ProgGenTH
import CFSF (Val(One))

import Criterion
import Criterion.Types
import Criterion.Main

benchTHTests :: IO ()
benchTHTests = do
    let ins' = [1..100000]
        ins = map One ins'
    single100 <- benchmarkSet "100" $$(makeProg11 100) (ins, ins')
    single200 <- benchmarkSet "200" $$(makeProg11 200) (ins, ins')
    single300 <- benchmarkSet "300" $$(makeProg11 300) (ins, ins')
    let benches = [single100, single200, single300]
    defaultMainWith (defaultConfig {csvFile = Just "random_out.csv"}) benches