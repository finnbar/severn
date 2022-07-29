module Scratchpad where

import ArrowNF

inner :: ANF (V Int) (V Int)
inner = loop $ arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)) >>> second (pre (One 0))

outer :: ANF (V Int) (V Int)
outer = loop $ first inner >>> arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)) >>> second (pre (One 0) >>> arr (\(One x) -> One $ x + 1))

innerl :: ANF (V Int) (V Int)
innerl = loop $ second (pre (One 0)) >>> arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a))

outerl :: ANF (V Int) (V Int)
outerl = loop $ second (pre (One 0) >>> arr (\(One x) -> One $ x + 1)) >>> first innerl >>> arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a))

f :: NoComp (V Int) (V Int)
f = Arr $ \(One x) -> One (x+1)

f' :: NoComp (P (V Int) (V Int)) (P (V Int) (V Int))
f' = Arr $ \(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)