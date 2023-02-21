module Scratchpad where

import ArrowNF

inner :: CF (V Int) (V Int)
inner = loop $ arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)) >>> second (pre (One 0))

outer :: CF (V Int) (V Int)
outer = loop $ first inner >>> arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)) >>> second (pre (One 0) >>> arr (\(One x) -> One $ x + 1))

innerl :: CF (V Int) (V Int)
innerl = loop $ second (pre (One 0)) >>> arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a))

outerl :: CF (V Int) (V Int)
outerl = loop $ second (pre (One 0) >>> arr (\(One x) -> One $ x + 1)) >>> first innerl >>> arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a))

f :: CF (V Int) (V Int)
f = Single fno

fno :: NoComp ('V Int) ('V Int)
fno = Arr $ \(One x) -> One (x+1)

f' :: CF (P (V Int) (V Int)) (P (V Int) (V Int))
f' = Single fno'

fno' :: NoComp ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int))
fno' = Arr $ \(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)

mergeCF :: CF (P (V Int) (V Int)) (V Int)
mergeCF = arr $ \(Pair (One a) (One b)) -> One $ a + b

splitCF :: CF (V Int) (P (V Int) (V Int))
splitCF = arr $ \(One a) -> Pair (One a) (One a)

rightCrushFail :: CF (V Int) (V Int)
rightCrushFail = loop rightCrushLB
rightCrushLB :: CF (P (V Int) (V Int)) (P (V Int) (V Int))
rightCrushLB = (f *** f) >>> second (splitCF >>> (f *** pre (One 0)) >>> (pre (One 0) *** f) >>> mergeCF >>> f)

dependsLoopM :: CF (V Int) (V Int)
dependsLoopM = loop dependsLoopMLB
dependsLoopMLB :: CF (P (V Int) (V Int)) (P (V Int) (V Int))
dependsLoopMLB = f' >>> second (loop (f' >>> pre (Pair (One 0) (One 0)) >>> f'))

trivialFail = loop $ (f *** f) >>> f' >>> second (pre (One 0))

tighteningNeeded = loop $ second mergeCF >>> f' >>> second (loop (f' >>> first splitCF >>> second (pre (One 0)) >>> first (first (pre (One 0)))) >>> second (pre (One 0)))