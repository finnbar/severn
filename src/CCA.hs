module CCA where

data CCNF a b where
  Arr :: (a -> b) -> CCNF a b
  LoopD :: c -> ((a, c) -> (b, c)) -> CCNF a b