module Scratchpad where

import ArrowCFSF

-- This file is a collection of functions you might want to use when testing this on the repl.

inner :: CFSF (V Int) (V Int)
inner = loop $ arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)) >>> second (pre (One 0))

outer :: CFSF (V Int) (V Int)
outer = loop $ first inner >>> arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)) >>> second (pre (One 0) >>> arr (\(One x) -> One $ x + 1))

innerl :: CFSF (V Int) (V Int)
innerl = loop $ second (pre (One 0)) >>> arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a))

outerl :: CFSF (V Int) (V Int)
outerl = loop $ second (pre (One 0) >>> arr (\(One x) -> One $ x + 1)) >>> first innerl >>> arr (\(Pair (One a) (One b)) -> Pair (One (a + b)) (One a))

f :: CFSF (V Int) (V Int)
f = Single fno

fno :: NoComp ('V Int) ('V Int)
fno = Arr $ \(One x) -> One (x+1)

f' :: CFSF (P (V Int) (V Int)) (P (V Int) (V Int))
f' = Single fno'

fno' :: NoComp ('P ('V Int) ('V Int)) ('P ('V Int) ('V Int))
fno' = Arr $ \(Pair (One a) (One b)) -> Pair (One (a + b)) (One a)

mergeCFSF :: CFSF (P (V Int) (V Int)) (V Int)
mergeCFSF = arr $ \(Pair (One a) (One b)) -> One $ a + b

splitCFSF :: CFSF (V Int) (P (V Int) (V Int))
splitCFSF = arr $ \(One a) -> Pair (One a) (One a)

rightCrushFail :: CFSF (V Int) (V Int)
rightCrushFail = loop rightCrushLB
rightCrushLB :: CFSF (P (V Int) (V Int)) (P (V Int) (V Int))
rightCrushLB = (f *** f) >>> second (splitCFSF >>> (f *** pre (One 0)) >>> (pre (One 0) *** f) >>> mergeCFSF >>> f)

dependsLoopM :: CFSF (V Int) (V Int)
dependsLoopM = loop dependsLoopMLB
dependsLoopMLB :: CFSF (P (V Int) (V Int)) (P (V Int) (V Int))
dependsLoopMLB = f' >>> second (loop (f' >>> pre (Pair (One 0) (One 0)) >>> f'))

trivialFail = loop $ (f *** f) >>> f' >>> second (pre (One 0))

tighteningNeeded = loop $ second mergeCFSF >>> f' >>> second (loop (f' >>> first splitCFSF >>> second (pre (One 0)) >>> first (first (pre (One 0)))) >>> second (pre (One 0)))