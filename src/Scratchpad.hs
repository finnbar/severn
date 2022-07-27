module Scratchpad where

import ArrowNF

inner :: ANF (V Int) (V Int)
inner = loop $ arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)) >>> second (pre (One 0))

outer :: ANF (V Int) (V Int)
outer = loop $ first inner >>> arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)) >>> second (pre (One 0))

f :: NoComp (V Int) (V Int)
f = Arr $ \(One x) -> One (x+1)