{-# LANGUAGE DataKinds, GADTs, ScopedTypeVariables, TypeApplications, PolyKinds,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}

module ArbitraryProgram where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import TestHelpers

import ArrowNF
import FRP.Yampa (SF, iPre)
import qualified Control.Arrow as A
import qualified Control.Category as C
import Data.Maybe (fromJust)
import Data.Proxy
import Transform

-- Finally: generate the structure loop ((f *** g) >>> h >>> (i *** j)), where decoupledness of f, i doesn't matter.
-- Then either:
-- 1. j >>> g is decoupled. So generate decoupled x and then slide a random amount of times. h is then not decoupled.
-- 2. h is decoupled. j and g therefore can be decoupled but don't need to be.
-- Assign a size to each of f, g, h, i, j when doing this which sums to our target size.
-- Okay! This is doable.

-- LOOP GENERATION

-- NOTE: We limit LoopD and LoopM to having at most two inputs.

makeLoop :: (ValidDesc a, ValidDesc b, ValidDesc c)
    => Maybe (ANF (P a c) (P b c), SF (Simplify (P a c)) (Simplify (P b c)))
    -> Maybe (ANF a b, SF (Simplify a) (Simplify b))
makeLoop myb = case myb of
    Just (anf, sf) -> Just (Single $ Loop anf, A.loop sf)
    Nothing -> Nothing

-- We refer to structure ((f *** g) >>> h >>> (i *** j))
genLoopM :: forall a b. (GenProg (P a (V Int)) (P b (V Int)),
    GenProg (P a (P (V Int) (V Int))) (P b (P (V Int) (V Int))),
    ValidDesc a, ValidDesc b, Reduce a, Reduce b)
    => Int -- size of loop (g, h, j)
    -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b))) -- Generator of LoopD
genLoopM l = Gen.choice [
        genLoopM' (Proxy :: Proxy (V Int)), -- One looped value
        genLoopM' (Proxy :: Proxy (P (V Int) (V Int))) -- A pair of looped values
    ]
    where
        genLoopM' :: forall s (v :: Desc s). (GenProg (P a v) (P b v), GenProg v v, ValidDesc v, Reduce a, Reduce b) =>
            Proxy v -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))
        genLoopM' pv = do
            -- A loop with looped value of type v
            let (ll, lr) = halve l
                f = Gen.constant $ Just genId
                i = Gen.constant $ Just genId
                h = genDecoupled (Proxy :: Proxy (P a v)) (Proxy :: Proxy (P b v)) ll
                (lrl, lrr) = halve lr
                g = genProg pv pv lrl
                j = genProg pv pv lrr
            makeLoop <$> maybeComp (maybeComp (maybePar f g) h) (maybePar i j)

genLoopD :: forall a b x y. (GenProg (P x (V Int)) (P y (V Int)),
    GenProg (P x (P (V Int) (V Int))) (P y (P (V Int) (V Int))),
    ValidDesc a, ValidDesc b, ValidDesc x, ValidDesc y)
    => Int -- size of loop (g, h, j)
    -> Gen (Maybe (ANF a x, SF (Simplify a) (Simplify x))) -- f
    -> Gen (Maybe (ANF y b, SF (Simplify y) (Simplify b))) -- i
    -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))
genLoopD l fgen igen = Gen.choice [
        genLoopD' (Proxy :: Proxy (V Int)), -- One looped value
        genLoopD' (Proxy :: Proxy (P (V Int) (V Int))) -- A pair of looped values
    ]
    where
        genLoopD' :: forall s (v :: Desc s). (GenProg (P x v) (P y v), GenProg v v, ValidDesc v, Reduce v) =>
            Proxy v -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))
        genLoopD' pv = do
            let (ll, lr) = halve l
                f = fgen
                i = igen
                h = genProg (Proxy :: Proxy (P x v)) (Proxy :: Proxy (P y v)) ll
                g = genDecoupled (Proxy :: Proxy v) (Proxy :: Proxy v) lr
                j = Gen.constant $ Just genId
            makeLoop <$> maybeComp (maybeComp (maybePar f g) h) (maybePar i j)

-- CLASS FOR GENERATION

class GenProg a b where
    genProg :: Proxy a -> Proxy b -> Int -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))
    genDecoupled :: Proxy a -> Proxy b -> Int -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))

-- Helper proxies to avoid long annotations throughout the code.
_1 :: Proxy (V Int)
_1 = Proxy
_2 :: Proxy (P (V Int) (V Int))
_2 = Proxy
_3a :: Proxy (P (P (V Int) (V Int)) (V Int))
_3a = Proxy
_3b :: Proxy (P (V Int) (P (V Int) (V Int)))
_3b = Proxy
_4 :: Proxy (P (P (V Int) (V Int)) (P (V Int) (V Int)))
_4 = Proxy

instance GenProg (V Int) (V Int) where
    genProg _1 __1 l
        | l < 1 = return $ Just genId
        | l == 1 = return $ Just arbitraryFn
        | otherwise =
            -- TODO We could have a LoopD
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genProg _1 _1 ll) (genProg _1 _1 lr),
                maybeComp (genProg _1 _2 ll) (genProg _2 _1 lr)]

    genDecoupled _1 __1 l
        | l < 1 = return Nothing
        | l == 1 = return $ Just genPre
        | otherwise =
            -- TODO We could have a LoopM
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genDecoupled _1 _1 ll) (genProg _1 _1 lr),
                maybeComp (genProg _1 _1 ll) (genDecoupled _1 _1 lr),
                maybeComp (genDecoupled _1 _2 ll) (genProg _2 _1 lr),
                maybeComp (genProg _1 _2 ll) (genDecoupled _2 _1 lr)]

instance GenProg (V Int) (P (V Int) (V Int)) where
    genProg _1 _2 l
        | l < 1 = return Nothing
        | l == 1 = return $ Just arbitraryFn
        | otherwise =
            -- TODO We could have a LoopD
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genProg _1 _2 ll) (genProg _2 _2 lr),
                maybeComp (genProg _1 _1 ll) (genProg _1 _2 lr)]

    genDecoupled _1 _2 l
        | l < 2 = return Nothing
        | otherwise =
            -- TODO We could have a LoopM
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genDecoupled _1 _1 ll) (genProg _1 _2 lr),
                maybeComp (genProg _1 _2 ll) (genDecoupled _2 _2 lr)
            ]

instance GenProg (P (V Int) (V Int)) (V Int) where
    genProg _2 _1 l
        | l < 1 = return Nothing
        | l == 1 = return $ Just arbitraryFn
        | otherwise =
            -- TODO We could have a LoopD
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genProg _2 _2 ll) (genProg _2 _1 lr),
                maybeComp (genProg _2 _1 ll) (genProg _1 _1 lr)]
    genDecoupled _2 _1 l
        | l < 2 = return Nothing
        | otherwise =
            -- TODO We could have a LoopM
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genDecoupled _2 _2 ll) (genProg _2 _1 lr),
                maybeComp (genProg _2 _1 ll) (genDecoupled _1 _1 lr)
            ]

instance GenProg (P (V Int) (V Int)) (P (V Int) (V Int)) where
    genProg _2 __2 l
        | l < 1 = return $ Just genId
        | l == 1 = return $ Just arbitraryFn
        | otherwise =
            -- TODO We could have a LoopD
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genProg _2 _2 ll) (genProg _2 _2 lr),
                maybeComp (genProg _2 _1 ll) (genProg _1 _2 lr),
                maybePar (genProg _1 _1 ll) (genProg _1 _1 lr),
                -- d *** x where x not decoupled is itself not decoupled
                -- (this is to test more complex situations)
                maybePar (genDecoupled _1 _1 ll) (genProg _1 _1 lr),
                maybePar (genProg _1 _1 ll) (genDecoupled _1 _1 lr)]
    genDecoupled _2 __2 l
        | l < 1 = return Nothing
        | l == 1 = return $ Just genPre
        | otherwise =
            -- TODO We could have a LoopM
            -- OR we could have a LoopD with partial Pre on its left edge, e.g.
            -- (genDecoupled _1 _1 ll) (genProg _1 _1 lr) (loopDWithPreOnSecondInput)
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genDecoupled _2 _2 ll) (genProg _2 _2 lr),
                maybeComp (genProg _2 _2 ll) (genDecoupled _2 _2 lr),
                maybeComp (genDecoupled _2 _1 ll) (genProg _1 _2 lr),
                maybeComp (genProg _2 _1 ll) (genDecoupled _1 _2 lr),
                maybePar (genDecoupled _1 _1 ll) (genDecoupled _1 _1 lr)]

-- TODO: we have no instances for 3a, 3b and 4 except for with themselves.
-- Might be worth adding some for more complex arrow programs.

instance GenProg (P (P (V Int) (V Int)) (V Int)) (P (P (V Int) (V Int)) (V Int)) where
    genProg _3a __3a l
        | l < 1 = return $ Just genId
        | l == 1 = return $ Just arbitraryFn
        | otherwise =
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genProg _3a _3a ll) (genProg _3a _3a lr),
                maybePar (genProg _2 _2 ll) (genProg _1 _1 lr),
                maybePar (genDecoupled _2 _2 ll) (genProg _1 _1 lr),
                maybePar (genProg _2 _2 ll) (genDecoupled _1 _1 lr)
            ]
    genDecoupled _3a __3a l
        | l < 1 = return Nothing
        | l == 1 = return $ Just genPre
        | otherwise =
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genDecoupled _3a _3a ll) (genProg _3a _3a lr),
                maybeComp (genProg _3a _3a ll) (genDecoupled _3a _3a lr),
                maybePar (genDecoupled _2 _2 ll) (genDecoupled _1 _1 lr)
            ]

instance GenProg (P (V Int) (P (V Int) (V Int))) (P (V Int) (P (V Int) (V Int))) where
    genProg _3b __3b l
        | l < 1 = return $ Just genId
        | l == 1 = return $ Just arbitraryFn
        | otherwise =
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genProg _3b _3b ll) (genProg _3b _3b lr),
                maybePar (genProg _1 _1 ll) (genProg _2 _2 lr),
                maybePar (genDecoupled _1 _1 ll) (genProg _2 _2 lr),
                maybePar (genProg _1 _1 ll) (genDecoupled _2 _2 lr)
            ]
    genDecoupled _3b __3b l
        | l < 1 = return Nothing
        | l == 1 = return $ Just genPre
        | otherwise =
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genDecoupled _3b _3b ll) (genProg _3b _3b lr),
                maybeComp (genProg _3b _3b ll) (genDecoupled _3b _3b lr),
                maybePar (genDecoupled _1 _1 ll) (genDecoupled _2 _2 lr)
            ]

instance GenProg (P (P (V Int) (V Int)) (P (V Int) (V Int))) (P (P (V Int) (V Int)) (P (V Int) (V Int))) where
    genProg _4 __4 l
        | l < 1 = return $ Just genId
        | l == 1 = return $ Just arbitraryFn
        | otherwise =
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genProg _4 _4 ll) (genProg _4 _4 lr),
                maybePar (genProg _2 _2 ll) (genProg _2 _2 lr),
                maybePar (genDecoupled _2 _2 ll) (genProg _2 _2 lr),
                maybePar (genProg _2 _2 ll) (genDecoupled _2 _2 lr)
            ]
    
    genDecoupled _4 __4 l
        | l < 1 = return Nothing
        | l == 1 = return $ Just genPre
        | otherwise =
            let (ll, lr) = halve l
            in chooseAndTry [
                maybeComp (genDecoupled _4 _4 ll) (genProg _4 _4 lr),
                maybeComp (genProg _4 _4 ll) (genDecoupled _4 _4 lr),
                maybePar (genDecoupled _2 _2 ll) (genDecoupled _2 _2 lr)
            ]

-- Split an int into two, the larger always being returned first.
halve :: Int -> (Int, Int)
halve i = (ceiling (fromIntegral i / 2), floor (fromIntegral i / 2))

maybeComp :: (ValidDesc a, ValidDesc b, ValidDesc c) => Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b))) -> Gen (Maybe (ANF b c, SF (Simplify b) (Simplify c))) ->
    Gen (Maybe (ANF a c, SF (Simplify a) (Simplify c)))
maybeComp = maybeMap (\(anfl, sfl) (anfr, sfr) -> (anfl >>> anfr, sfl A.>>> sfr))

maybePar :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d) => Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b))) -> Gen (Maybe (ANF c d, SF (Simplify c) (Simplify d))) ->
    Gen (Maybe (ANF (P a c) (P b d), SF (Simplify a, Simplify c) (Simplify b, Simplify d)))
maybePar = maybeMap (\(anfl, sfl) (anfr, sfr) -> (anfl *** anfr, sfl A.*** sfr))

debugSample :: Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b))) -> IO ()
debugSample gen = do
    (anf, sf) <- fromJust <$> Gen.sample gen
    print anf

-- GENERATE FUNCTIONS OF ARBITRARY ARITY

arbitraryFn :: forall d d'. (Reduce d, Duplicate d') =>
    (ANF d d', SF (Simplify d) (Simplify d'))
arbitraryFn = let
    (anfl, sfl) = reduce @d
    (anfr, sfr) = duplicate @d'
    in (Single . Arr $ anfr . anfl, A.arr $ sfr . sfl)

genPre :: forall d. (Reduce d) => (ANF d d, SF (Simplify d) (Simplify d))
genPre = let (zl, zr) = genZero in (pre_ zl, iPre zr)

class ValidDesc a => Reduce a where
    reduce :: (Val a -> Val (V Int), Simplify a -> Int)
    genId :: (ANF a a, SF (Simplify a) (Simplify a))
    genZero :: (Val a, Simplify a)

instance Reduce (V Int) where
    reduce = (Prelude.id, Prelude.id)
    genId = (id_, C.id)
    genZero = (One 0, 0)

instance forall l r. (Reduce l, Reduce r) => Reduce (P l r) where
    reduce = let
        (anfl, sfl) = reduce @l
        (anfr, sfr) = reduce @r
        in (\(Pair x y) ->
            let One x' = anfl x
                One y' = anfr y
            in One $ x' + y',
            \(x,y) -> sfl x + sfr y)
    genId = (id_, C.id)
    genZero = let
        (vl, il) = genZero @l
        (vr, ir) = genZero @r
        in (Pair vl vr, (il, ir))
        
class ValidDesc a => Duplicate a where
    duplicate :: ValidDesc a => (Val (V Int) -> Val a, Int -> Simplify a)

instance Duplicate (V Int) where
    duplicate = (Prelude.id, Prelude.id)

instance forall l r. (Duplicate l, Duplicate r) => Duplicate (P l r) where
    duplicate = let
        (anfl, sfl) = duplicate @l
        (anfr, sfr) = duplicate @r
        in (\x -> Pair (anfl x) (anfr x), \x -> (sfl x, sfr x))