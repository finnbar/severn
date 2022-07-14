{-# LANGUAGE TemplateHaskell #-}

module SpecTH where

import Language.Haskell.TH

dup :: Q Exp -> Q Exp
dup e = [| ($e, $e) |]