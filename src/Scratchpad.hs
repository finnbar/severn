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

f :: ANF (V Int) (V Int)
f = Single fno

fno :: NoComp ('V Int) ('V Int)
fno = Arr $ \(One x) -> One (x+1)

f' :: ANF (P (V Int) (V Int)) (P (V Int) (V Int))
f' = Single fno'

fno' :: NoComp ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int))
fno' = Arr $ \(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)

mergeANF :: ANF (P (V Int) (V Int)) (V Int)
mergeANF = arr $ \(Pair (One a) (One b)) -> One $ a + b

splitANF :: ANF (V Int) (P (V Int) (V Int))
splitANF = arr $ \(One a) -> Pair (One a) (One a)

rightCrushFail :: ANF (V Int) (V Int)
rightCrushFail = loop rightCrushLB
rightCrushLB :: ANF (P (V Int) (V Int)) (P (V Int) (V Int))
rightCrushLB = (f *** f) >>> second (splitANF >>> (f *** pre (One 0)) >>> (pre (One 0) *** f) >>> mergeANF >>> f)

dependsLoopM :: ANF (V Int) (V Int)
dependsLoopM = loop dependsLoopMLB
dependsLoopMLB :: ANF (P (V Int) (V Int)) (P (V Int) (V Int))
dependsLoopMLB = f' >>> second (loop (f' >>> pre (Pair (One 0) (One 0)) >>> f'))

trivialFail = loop $ (f *** f) >>> f' >>> second (pre (One 0))