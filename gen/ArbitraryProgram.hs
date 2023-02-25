{-# LANGUAGE DataKinds, GADTs, ScopedTypeVariables, PolyKinds, TypeOperators,
    FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, StandaloneKindSignatures #-}

module ArbitraryProgram where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import TestHelpers

import ArrowCFSF
import FRP.Yampa (SF, iPre)
import qualified Control.Arrow as A
import qualified Control.Category as C
import Data.Maybe (fromJust)
import Data.Type.Equality (type (:~~:)(..))

-- A PROXY-LIKE FOR DESCRIPTORS

type PDesc :: forall s. Desc s -> *
data PDesc x where
    ProxV :: PDesc (V Double)
    ProxP :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> PDesc (P a b)

pDescEq :: PDesc a -> PDesc b -> Maybe (a :~~: b)
pDescEq ProxV ProxV = Just HRefl
pDescEq (ProxP a b) (ProxP a' b') = do
    HRefl <- pDescEq a a'
    HRefl <- pDescEq b b'
    return HRefl
pDescEq _ _ = Nothing

-- GENERATION PARAMETERS

data GenParam = GP {
        size :: Int, -- How many blocks we're allowed in the generated program.
        loopWeighting :: (Int, Int) -- How much to weight making a loop vs not.
        -- (l, n) => choose loop l/(n+l) times, choose no loop n/(n+l) times.
    } deriving Show

weightedOnLoop :: GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
    -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
    -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
weightedOnLoop gp loopy nonloopy =
    let (l, n) = loopWeighting gp
    in Gen.frequency [(l, loopy), (n, nonloopy)]

-- Split a GenParam into two which sum to the original GenParam.
-- Allows us to separate requirements (on number of program elements / loop structure).
splitBetween :: GenParam -> (GenParam, GenParam)
splitBetween gp =
    let (s,s') = halve (size gp)
        lw = loopWeighting gp
    in (GP s lw, GP s' lw)
    where
        halve :: Int -> (Int, Int)
        halve i = (ceiling (fromIntegral i / 2), floor (fromIntegral i / 2))

maybeComp :: (ValidDesc a, ValidDesc b, ValidDesc c) => Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b))) -> Gen (Maybe (CFSF b c, SF (Simplify b) (Simplify c))) ->
    Gen (Maybe (CFSF a c, SF (Simplify a) (Simplify c)))
maybeComp = maybeMap (\(cfsfl, sfl) (cfsfr, sfr) -> (cfsfl >>> cfsfr, sfl A.>>> sfr))

maybePar :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d) => Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b))) -> Gen (Maybe (CFSF c d, SF (Simplify c) (Simplify d))) ->
    Gen (Maybe (CFSF (P a c) (P b d), SF (Simplify a, Simplify c) (Simplify b, Simplify d)))
maybePar = maybeMap (\(cfsfl, sfl) (cfsfr, sfr) -> (cfsfl *** cfsfr, sfl A.*** sfr))

debugSample :: Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b))) -> IO ()
debugSample gen = do
    (cfsf, sf) <- fromJust <$> Gen.sample gen
    print cfsf

-- LOOP GENERATION

-- Finally: generate the structure loop ((f *** g) >>> h >>> (i *** j)), where decoupledness of f, i doesn't matter.
-- Then either:
-- 1. j >>> g is decoupled. So generate decoupled x and then slide a random amount of times. h is then not decoupled.
-- 2. h is decoupled. j and g therefore can be decoupled but don't need to be.
-- Assign a size to each of f, g, h, i, j when doing this which sums to our target size.
-- Okay! This is doable.

makeLoop :: (ValidDesc a, ValidDesc b, ValidDesc c)
    => Maybe (CFSF (P a c) (P b c), SF (Simplify (P a c)) (Simplify (P b c)))
    -> Maybe (CFSF a b, SF (Simplify a) (Simplify b))
makeLoop myb = case myb of
    Just (cfsf, sf) -> Just (Single $ Loop cfsf, A.loop sf)
    Nothing -> Nothing

-- We refer to structure ((f *** g) >>> h >>> (i *** j))
genLoopM :: forall a b. (ValidDesc a, ValidDesc b)
    => PDesc a -> PDesc b
    -> GenParam
    -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b))) -- Generator of LoopD
genLoopM pa pb gp =
        Gen.choice [
            genLoopM' ProxV gp, -- One looped value
            genLoopM' (ProxP ProxV ProxV) gp -- A pair of looped values
        ]
    where
        genLoopM' :: forall s (v :: Desc s). (ValidDesc v) =>
            PDesc v -> GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
        genLoopM' pv gp' = do
            -- A loop with looped value of type v
            let (gpl, gpr) = splitBetween gp'
                f = Gen.constant $ Just $! genId pa
                i = Gen.constant $ Just $! genId pb
                h = genDecoupled (ProxP pa pv) (ProxP pb pv) gpl
                (gprl, gprr) = splitBetween gpr
                g = genProg pv pv gprl
                j = genProg pv pv gprr
            makeLoop <$> maybeComp (maybeComp (maybePar f g) h) (maybePar i j)

genLoopD :: forall a b x y. (ValidDesc a, ValidDesc b, ValidDesc x, ValidDesc y)
    => PDesc x -> PDesc y
    -> GenParam -- size of loop (g, h, j)
    -> Gen (Maybe (CFSF a x, SF (Simplify a) (Simplify x))) -- f
    -> Gen (Maybe (CFSF y b, SF (Simplify y) (Simplify b))) -- i
    -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
genLoopD px py gp fgen igen = 
        Gen.choice [
            genLoopD' ProxV gp, -- One looped value
            genLoopD' (ProxP ProxV ProxV) gp -- A pair of looped values
        ]
    where
        genLoopD' :: forall s (v :: Desc s). (ValidDesc v) =>
            PDesc v -> GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
        genLoopD' pv gp' = do
            let (gpl, gpr) = splitBetween gp'
                f = fgen
                i = igen
                h = genProg (ProxP px pv) (ProxP py pv) gpl
                g = genDecoupled pv pv gpr
                j = Gen.constant . Just $! genId pv
            makeLoop <$> maybeComp (maybeComp (maybePar f g) h) (maybePar i j)

-- CLASS FOR GENERATION

genProg :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
genProg pa pb gp =
    case pDescEq pa pb of
        Just HRefl -> genProgEqTypes pa gp
        Nothing -> genProgDiffTypes pa pb gp
    where
        genProgEqTypes :: ValidDesc a => PDesc a -> GenParam -> Gen (Maybe (CFSF a a, SF (Simplify a) (Simplify a)))
        genProgEqTypes pa gp
            | size gp < 1 = return . Just $! genId pa
            | size gp == 1 = return . Just $! arbitraryFn pa pa
            | otherwise = case pa of
                ProxV ->
                    let (gpl, gpr) = splitBetween gp
                    in weightedOnLoop gp
                        (genLoopD ProxV ProxV gp (Gen.constant (Just $! genId ProxV)) (Gen.constant (Just $! genId ProxV))) $
                        chooseAndTry [
                            maybeComp (genProg ProxV ProxV gpl) (genProg ProxV ProxV gpr),
                            maybeComp (genProg ProxV (ProxP ProxV ProxV) gpl) (genProg (ProxP ProxV ProxV) ProxV gpr)]
                p@(ProxP a b) ->
                    let (gpl, gpr) = splitBetween gp
                    in weightedOnLoop gp
                        (genLoopD p p gp (Gen.constant (Just $ genId p)) (Gen.constant (Just $ genId p))) $
                        chooseAndTry [
                            -- Same type
                            maybeComp (genProg p p gpl) (genProg p p gpr),
                            -- Reduce down one size
                            maybeComp (genProg p a gpl) (genProg a p gpr),
                            maybeComp (genProg p b gpl) (genProg b p gpr),
                            -- Go up one size
                            maybeComp (genProg p (ProxP p ProxV) gpl) (genProg (ProxP p ProxV) p gpr),
                            maybeComp (genProg p (ProxP ProxV p) gpl) (genProg (ProxP ProxV p) p gpr),
                            -- Pair of the two inputs
                            maybePar (genProg a a gpl) (genProg b b gpr),
                            -- They can be half decoupled
                            maybePar (genDecoupled a a gpl) (genProg b b gpr),
                            maybePar (genProg a a gpl) (genDecoupled b b gpr)]
        genProgDiffTypes :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
        genProgDiffTypes pa pb gp
            | size gp < 1 = return Nothing
            | size gp == 1 = return . Just $! arbitraryFn pa pb
            | otherwise = 
                let (gpl, gpr) = splitBetween gp
                in weightedOnLoop gp
                    (genLoopD pa pb gp (Gen.constant (Just $ genId pa)) (Gen.constant (Just $ genId pb))) $
                    chooseAndTry [
                        maybeComp (genProg pa pa gpl) (genProg pa pb gpr),
                        maybeComp (genProg pa pb gpl) (genProg pb pb gpr)]

genDecoupled :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
genDecoupled pa pb gp =
    case pDescEq pa pb of
        Just HRefl -> genDecoupledEqTypes pa gp
        Nothing -> if size gp < 2 then return Nothing else
            let (gpl, gpr) = splitBetween gp
                gens = gensDecoupledPair pa pb pb gpl gpr
                    ++ gensDecoupledPair pa pa pb gpl gpr
            in weightedOnLoop gp
                (genLoopM pa pb gp)
                (chooseAndTry gens)
    where
        genDecoupledEqTypes :: ValidDesc a => PDesc a -> GenParam -> Gen (Maybe (CFSF a a, SF (Simplify a) (Simplify a)))
        genDecoupledEqTypes pa gp
            | size gp < 1 = return Nothing
            | size gp == 1 = return . Just $! genPre pa
            | otherwise = case pa of
                ProxV -> 
                    let (gpl, gpr) = splitBetween gp
                        gens = gensDecoupledPair ProxV ProxV ProxV gpl gpr
                            ++ gensDecoupledPair ProxV (ProxP ProxV ProxV) ProxV gpl gpr
                    in weightedOnLoop gp
                        (genLoopM ProxV ProxV gp)
                        (chooseAndTry gens)
                p@(ProxP a b) ->
                    let (gpl, gpr) = splitBetween gp
                        gensC = gensDecoupledPair p p p gpl gpr ++
                                gensDecoupledPair p a p gpl gpr ++
                                gensDecoupledPair p b p gpl gpr ++
                                gensDecoupledPair p (ProxP p ProxV) p gpl gpr ++
                                gensDecoupledPair p (ProxP ProxV p) p gpl gpr
                        gensL = genLoopM p p gp :
                                genDecouplingWithinLoopD a b gp
                        gensP = maybePar (genDecoupled a a gpl) (genDecoupled b b gpr)
                    in weightedOnLoop gp
                        (chooseAndTry gensL)
                        (chooseAndTry $ gensP : gensC)
        genDecouplingWithinLoopD :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> GenParam -> [Gen (Maybe (CFSF (P a b) (P a b), SF (Simplify a, Simplify b) (Simplify a, Simplify b)))]
        genDecouplingWithinLoopD pa pb gp =
            let (gp1, gp2) = splitBetween gp
                (gp3, gp4) = splitBetween gp1
                (gp5, gp6) = splitBetween gp2
            in [
                -- (nodec *** dec) >>> LoopD with (Pre *** f) left tightenable
                -- nodec *** dec
                maybeComp (maybePar (genProg pa pa gp3) (genDecoupled pb pb gp4))
                    -- LoopD...
                    (genLoopD (ProxP pa pb) (ProxP pa pb) gp5
                        -- with dec *** nodec
                        (maybePar (genDecoupled pa pa gp6) (Gen.constant $ Just $! genId pb)) (Gen.constant (Just $! genId (ProxP pa pb)))),
                -- LoopD with (f *** Pre) right tightenable >>> (dec *** nodec)
                -- LoopD...
                maybeComp (genLoopD (ProxP pa pb) (ProxP pa pb) gp3
                    -- with right tightenable nodec *** dec
                    (Gen.constant (Just $! genId (ProxP pa pb))) (maybePar (Gen.constant $ Just $! genId pa) (genDecoupled pb pb gp4)))
                    -- dec *** nodec
                    (maybePar (genDecoupled pa pa gp5) (genProg pb pb gp6))
                ]

gensDecoupledPair :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
    PDesc a -> PDesc b -> PDesc c -> GenParam -> GenParam -> [Gen (Maybe (CFSF a c, SF (Simplify a) (Simplify c)))]
gensDecoupledPair pa pb pc gpl gpr = [
        maybeComp (genProg pa pb gpl) (genDecoupled pb pc gpr),
        maybeComp (genDecoupled pa pb gpl) (genProg pb pc gpr),
        maybeComp (genDecoupled pa pb gpl) (genDecoupled pb pc gpr)
    ]

-- GENERATE FUNCTIONS OF ARBITRARY ARITY

arbitraryFn :: (ValidDesc d, ValidDesc d') => PDesc d -> PDesc d' ->
    (CFSF d d', SF (Simplify d) (Simplify d'))
arbitraryFn d d' = let
    (cfsfl, sfl) = reduce d
    (cfsfr, sfr) = duplicate d'
    in (Single . Arr $ cfsfr . cfsfl, A.arr $ sfr . sfl)

reduce :: PDesc d -> (Val d -> Val (V Double), Simplify d -> Double)
reduce ProxV = (\(One x) -> One (x/1.1), (/1.1))
reduce (ProxP a b) =
    let
        (cfsfl, sfl) = reduce a
        (cfsfr, sfr) = reduce b
    in (\(Pair x y) ->
            let One x' = cfsfl x
                One y' = cfsfr y
            in if x' /= 0 then One (y'+x') else One y',
        \(x,y) -> 
            let x' = sfl x
                y' = sfr y
            in if x' /= 0 then y'+x' else y')

duplicate :: PDesc d -> (Val (V Double) -> Val d, Double -> Simplify d)
duplicate ProxV = (\(One x) -> One (x+1.1), (+1.1))
duplicate (ProxP a b) =
    let
        (cfsfl, sfl) = duplicate a
        (cfsfr, sfr) = duplicate b
    in (\x -> Pair (cfsfl x) (cfsfr x), \x -> (sfl x, sfr x))

genPre :: ValidDesc d => PDesc d -> (CFSF d d, SF (Simplify d) (Simplify d))
genPre pd = let (zl, zr) = genZero pd in (pre_ zl, iPre zr)

genId :: ValidDesc d => PDesc d -> (CFSF d d, SF (Simplify d) (Simplify d))
genId _ = (id_, C.id)

genZero :: PDesc a -> (Val a, Simplify a)
genZero ProxV = (One 0, 0)
genZero (ProxP a b) =
    let (cfsfl, sfl) = genZero a
        (cfsfr, sfr) = genZero b
    in (Pair cfsfl cfsfr, (sfl, sfr))