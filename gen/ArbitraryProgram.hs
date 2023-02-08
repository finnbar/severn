{-# LANGUAGE DataKinds, GADTs, ScopedTypeVariables, PolyKinds, TypeOperators,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, StandaloneKindSignatures #-}

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
import Data.Type.Equality (type (:~~:)(..))

-- A PROXY-LIKE FOR DESCRIPTORS

type PDesc :: forall s. Desc s -> *
data PDesc x where
    ProxV :: PDesc (V Int)
    ProxP :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> PDesc (P a b)

pDescEq :: PDesc a -> PDesc b -> Maybe (a :~~: b)
pDescEq ProxV ProxV = Just HRefl
pDescEq (ProxP a b) (ProxP a' b') = do
    HRefl <- pDescEq a a'
    HRefl <- pDescEq b b'
    return HRefl
pDescEq _ _ = Nothing

-- GENERATION PARAMETERS

-- TODO: Actually use this.
data GenParam = GP {
        size :: Int, -- How many blocks we're allowed in the generated program.
        loopCount :: Int, -- How many loops we're allowed to create.
        branching :: Int -> (Int, Int) -- How to split loopCount between the loop we're creating and future loops.
    }

-- LOOP GENERATION

-- Finally: generate the structure loop ((f *** g) >>> h >>> (i *** j)), where decoupledness of f, i doesn't matter.
-- Then either:
-- 1. j >>> g is decoupled. So generate decoupled x and then slide a random amount of times. h is then not decoupled.
-- 2. h is decoupled. j and g therefore can be decoupled but don't need to be.
-- Assign a size to each of f, g, h, i, j when doing this which sums to our target size.
-- Okay! This is doable.

-- TODO Nested loop generation.
-- 1. Add a loop count variable. Probably replace the Int input with some kind of size data type containing multiple fields. Use this to determine whether to nest.

makeLoop :: (ValidDesc a, ValidDesc b, ValidDesc c)
    => Maybe (ANF (P a c) (P b c), SF (Simplify (P a c)) (Simplify (P b c)))
    -> Maybe (ANF a b, SF (Simplify a) (Simplify b))
makeLoop myb = case myb of
    Just (anf, sf) -> Just (Single $ Loop anf, A.loop sf)
    Nothing -> Nothing

-- We refer to structure ((f *** g) >>> h >>> (i *** j))
genLoopM :: forall a b. (ValidDesc a, ValidDesc b)
    => PDesc a -> PDesc b
    -> Int -- size of loop (g, h, j)
    -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b))) -- Generator of LoopD
genLoopM pa pb l = Gen.choice [
        genLoopM' ProxV, -- One looped value
        genLoopM' (ProxP ProxV ProxV) -- A pair of looped values
    ]
    where
        genLoopM' :: forall s (v :: Desc s). (ValidDesc v) =>
            PDesc v -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))
        genLoopM' pv = do
            -- A loop with looped value of type v
            let (ll, lr) = halve l
                f = Gen.constant $ Just $ genId pa
                i = Gen.constant $ Just $ genId pb
                h = genDecoupled (ProxP pa pv) (ProxP pb pv) ll
                (lrl, lrr) = halve lr
                g = genProg pv pv lrl
                j = genProg pv pv lrr
            makeLoop <$> maybeComp (maybeComp (maybePar f g) h) (maybePar i j)

genLoopD :: forall a b x y. (ValidDesc a, ValidDesc b, ValidDesc x, ValidDesc y)
    => PDesc x -> PDesc y
    -> Int -- size of loop (g, h, j)
    -> Gen (Maybe (ANF a x, SF (Simplify a) (Simplify x))) -- f
    -> Gen (Maybe (ANF y b, SF (Simplify y) (Simplify b))) -- i
    -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))
genLoopD px py l fgen igen = Gen.choice [
        genLoopD' ProxV, -- One looped value
        genLoopD' (ProxP ProxV ProxV) -- A pair of looped values
    ]
    where
        genLoopD' :: forall s (v :: Desc s). (ValidDesc v) =>
            PDesc v -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))
        genLoopD' pv = do
            let (ll, lr) = halve l
                f = fgen
                i = igen
                h = genProg (ProxP px pv) (ProxP py pv) ll
                g = genDecoupled pv pv lr
                j = Gen.constant . Just $ genId pv
            makeLoop <$> maybeComp (maybeComp (maybePar f g) h) (maybePar i j)

-- CLASS FOR GENERATION

genProg :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> Int -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))
genProg pa pb l =
    case pDescEq pa pb of
        Just HRefl -> genProgEqTypes pa l
        Nothing -> genProgDiffTypes pa pb l
    where
        genProgEqTypes :: ValidDesc a => PDesc a -> Int -> Gen (Maybe (ANF a a, SF (Simplify a) (Simplify a)))
        genProgEqTypes pa l
            | l < 1 = return . Just $ genId pa
            | l == 1 = return . Just $ arbitraryFn pa pa
            | otherwise = case pa of
                ProxV ->
                    let (ll, lr) = halve l
                    in chooseAndTry [
                            maybeComp (genProg ProxV ProxV ll) (genProg ProxV ProxV lr),
                            maybeComp (genProg ProxV (ProxP ProxV ProxV) ll) (genProg (ProxP ProxV ProxV) ProxV lr),
                            genLoopD ProxV ProxV l (Gen.constant (Just $ genId ProxV)) (Gen.constant (Just $ genId ProxV))]
                p@(ProxP a b) ->
                    let (ll, lr) = halve l
                    in chooseAndTry [
                            -- Same type
                            maybeComp (genProg p p ll) (genProg p p lr),
                            -- Reduce down one size
                            maybeComp (genProg p a ll) (genProg a p lr),
                            maybeComp (genProg p b ll) (genProg b p lr),
                            -- Go up one size
                            maybeComp (genProg p (ProxP p ProxV) ll) (genProg (ProxP p ProxV) p lr),
                            maybeComp (genProg p (ProxP ProxV p) ll) (genProg (ProxP ProxV p) p lr),
                            -- Pair of the two inputs
                            maybePar (genProg a a ll) (genProg b b lr),
                            -- They can be half decoupled
                            maybePar (genDecoupled a a ll) (genProg b b lr),
                            maybePar (genProg a a ll) (genDecoupled b b lr),
                            genLoopD p p l (Gen.constant (Just $ genId p)) (Gen.constant (Just $ genId p))]
        genProgDiffTypes :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> Int -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))
        genProgDiffTypes pa pb l
            | l < 1 = return Nothing
            | l == 1 = return . Just $ arbitraryFn pa pb
            | otherwise = 
                let (ll, lr) = halve l
                in chooseAndTry [
                        maybeComp (genProg pa pa ll) (genProg pa pb lr),
                        maybeComp (genProg pa pb ll) (genProg pb pb lr),
                        genLoopD pa pb l (Gen.constant (Just $ genId pa)) (Gen.constant (Just $ genId pb))]

genDecoupled :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> Int -> Gen (Maybe (ANF a b, SF (Simplify a) (Simplify b)))
genDecoupled pa pb l =
    case pDescEq pa pb of
        Just HRefl -> genDecoupledEqTypes pa l 
        Nothing -> if l < 2 then return Nothing else
            let (ll, lr) = halve l
                gens = gensDecoupledPair pa pb pb ll lr
                    ++ gensDecoupledPair pa pa pb ll lr
                    ++ [genLoopM pa pb l]
            in chooseAndTry gens
    where
        genDecoupledEqTypes :: ValidDesc a => PDesc a -> Int -> Gen (Maybe (ANF a a, SF (Simplify a) (Simplify a)))
        genDecoupledEqTypes pa l
            | l < 1 = return Nothing
            | l == 1 = return $ Just $ genPre pa
            | otherwise = case pa of
                ProxV -> 
                    let (ll, lr) = halve l
                        gens = gensDecoupledPair ProxV ProxV ProxV ll lr
                            ++ gensDecoupledPair ProxV (ProxP ProxV ProxV) ProxV ll lr
                            ++ [genLoopM ProxV ProxV l]
                    in chooseAndTry gens
                p@(ProxP a b) ->
                    let (ll, lr) = halve l
                        gensC = gensDecoupledPair p p p ll lr ++
                                gensDecoupledPair p a p ll lr ++
                                gensDecoupledPair p b p ll lr ++
                                gensDecoupledPair p (ProxP p ProxV) p ll lr ++
                                gensDecoupledPair p (ProxP ProxV p) p ll lr ++
                                [genLoopM p p l] ++
                                genDecouplingWithinLoopD a b l
                        gensP = maybePar (genDecoupled a a ll) (genDecoupled b b lr)
                    in chooseAndTry $ gensP : gensC
        genDecouplingWithinLoopD :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> Int -> [Gen (Maybe (ANF (P a b) (P a b), SF (Simplify a, Simplify b) (Simplify a, Simplify b)))]
        genDecouplingWithinLoopD pa pb l =
            let (la, lb) = halve l
                (ll, lr) = halve la
                (ls, lt) = halve lb
            in [
                -- (nodec *** dec) >>> LoopD with (Pre *** f) left tightenable
                -- nodec *** dec
                maybeComp (maybePar (genProg pa pa ll) (genDecoupled pb pb lr))
                    -- LoopD...
                    (genLoopD (ProxP pa pb) (ProxP pa pb) ls
                        -- with dec *** nodec
                        (maybePar (genDecoupled pa pa lt) (Gen.constant $ Just $ genId pb)) (Gen.constant (Just $ genId (ProxP pa pb)))),
                -- LoopD with (f *** Pre) right tightenable >>> (dec *** nodec)
                -- LoopD...
                maybeComp (genLoopD (ProxP pa pb) (ProxP pa pb) ls
                    -- with right tightenable nodec *** dec
                    (Gen.constant (Just $ genId (ProxP pa pb))) (maybePar (Gen.constant $ Just $ genId pa) (genDecoupled pb pb ll)))
                    -- dec *** nodec
                    (maybePar (genDecoupled pa pa lr) (genProg pb pb lt))
                ]

gensDecoupledPair :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
    PDesc a -> PDesc b -> PDesc c -> Int -> Int -> [Gen (Maybe (ANF a c, SF (Simplify a) (Simplify c)))]
gensDecoupledPair pa pb pc ll lr = [
        maybeComp (genProg pa pb ll) (genDecoupled pb pc lr),
        maybeComp (genDecoupled pa pb ll) (genProg pb pc lr),
        maybeComp (genDecoupled pa pb ll) (genDecoupled pb pc lr)
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

arbitraryFn :: (ValidDesc d, ValidDesc d') => PDesc d -> PDesc d' ->
    (ANF d d', SF (Simplify d) (Simplify d'))
arbitraryFn d d' = let
    (anfl, sfl) = reduce d
    (anfr, sfr) = duplicate d'
    in (Single . Arr $ anfr . anfl, A.arr $ sfr . sfl)

reduce :: PDesc d -> (Val d -> Val (V Int), Simplify d -> Int)
reduce ProxV = (Prelude.id, Prelude.id)
reduce (ProxP a b) =
    let
        (anfl, sfl) = reduce a
        (anfr, sfr) = reduce b
    in (\(Pair x y) ->
            let One x' = anfl x
                One y' = anfr y
            in One $ x' + y',
        \(x,y) -> sfl x + sfr y)

duplicate :: PDesc d -> (Val (V Int) -> Val d, Int -> Simplify d)
duplicate ProxV = (Prelude.id, Prelude.id)
duplicate (ProxP a b) =
    let
        (anfl, sfl) = duplicate a
        (anfr, sfr) = duplicate b
    in (\x -> Pair (anfl x) (anfr x), \x -> (sfl x, sfr x))

genPre :: ValidDesc d => PDesc d -> (ANF d d, SF (Simplify d) (Simplify d))
genPre pd = let (zl, zr) = genZero pd in (pre_ zl, iPre zr)

genId :: ValidDesc d => PDesc d -> (ANF d d, SF (Simplify d) (Simplify d))
genId _ = (id_, C.id)

genZero :: PDesc a -> (Val a, Simplify a)
genZero ProxV = (One 0, 0)
genZero (ProxP a b) =
    let (anfl, sfl) = genZero a
        (anfr, sfr) = genZero b
    in (Pair anfl anfr, (sfl, sfr))