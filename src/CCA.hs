module CCA where

data CCNF a b where
  ArrCCNF :: (a -> b) -> CCNF a b
  LoopPreCCNF :: c -> ((a, c) -> (b, c)) -> CCNF a b