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
-- This allows us to say what arity we would like our generated SFs/CFSFs to be.

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
        loopCount :: Int -- How many loops this program should contain.
    } deriving Show

makeGenParam :: Int -> Double -> GenParam
makeGenParam size loopProportion = GP size (floor (fromIntegral size * loopProportion))

allowIfNoLoopNeeded :: GenParam -> Maybe a -> Maybe a
allowIfNoLoopNeeded gp ma = if loopCount gp == 0 then ma else Nothing

-- Split a GenParam into two which sum to the original GenParam.
-- Allows us to separate requirements (on number of program elements / loop count).
splitBetween :: GenParam -> (GenParam, GenParam)
splitBetween gp =
    let (s,s') = halve (size gp)
        (lc, lc') = halve (loopCount gp)
    in (GP s lc, GP s' lc')
    where
        halve :: Int -> (Int, Int)
        halve i = (ceiling (fromIntegral i / 2), floor (fromIntegral i / 2))

-- This attempts to use up a loop requirement.
useUpLoopRequirement :: GenParam -> Maybe GenParam
useUpLoopRequirement gp =
    let lc = loopCount gp
    in if lc > 0 then Just (gp {loopCount = lc - 1}) else Nothing

maybeComp :: (ValidDesc a, ValidDesc b, ValidDesc c) => Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b))) -> Gen (Maybe (CFSF b c, SF (Simplify b) (Simplify c))) ->
    Gen (Maybe (CFSF a c, SF (Simplify a) (Simplify c)))
maybeComp = maybeMap compPair

compPair :: (ValidDesc a, ValidDesc b, ValidDesc c) => (CFSF a b, SF (Simplify a) (Simplify b)) ->
    (CFSF b c, SF (Simplify b) (Simplify c)) -> (CFSF a c, SF (Simplify a) (Simplify c))
compPair (cfsfl, sfl) (cfsfr, sfr) = (cfsfl >>> cfsfr, sfl A.>>> sfr)

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
genLoopM pa pb gp = case useUpLoopRequirement gp of
    Just gp' ->
        Gen.choice [
            genLoopM' ProxV gp', -- One looped value
            genLoopM' (ProxP ProxV ProxV) gp' -- A pair of looped values
        ]
    Nothing -> return Nothing
    where
        genLoopM' :: forall s (v :: Desc s). (ValidDesc v) =>
            PDesc v -> GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
        genLoopM' pv gp' = do
            -- A loop with looped value of type v
            let (gpl, gpr) = splitBetween gp'
                f = Gen.constant $ Just $ genId pa
                i = Gen.constant $ Just $ genId pb
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
genLoopD px py gp fgen igen = case useUpLoopRequirement gp of
    Just gp' ->
        Gen.choice [
            genLoopD' ProxV gp', -- One looped value
            genLoopD' (ProxP ProxV ProxV) gp' -- A pair of looped values
        ]
    Nothing -> return Nothing
    where
        genLoopD' :: forall s (v :: Desc s). (ValidDesc v) =>
            PDesc v -> GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
        genLoopD' pv gp' = do
            let (gpl, gpr) = splitBetween gp'
                f = fgen
                i = igen
                h = genProg (ProxP px pv) (ProxP py pv) gpl
                g = genDecoupled pv pv gpr
                j = Gen.constant . Just $ genId pv
            makeLoop <$> maybeComp (maybeComp (maybePar f g) h) (maybePar i j)

-- CLASS FOR GENERATION

-- Generate a non-decoupled program of the arity described by @pa@ and @pb@.
genProg :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
genProg pa pb gp =
    case pDescEq pa pb of
        Just HRefl -> genProgEqTypes pa gp
        Nothing -> genProgDiffTypes pa pb gp
    where
        -- If the programs have the same types, we can return id.
        -- Otherwise, the program of size one is an arbitrary arr, and then larger programs are composed from that.
        genProgEqTypes :: ValidDesc a => PDesc a -> GenParam -> Gen (Maybe (CFSF a a, SF (Simplify a) (Simplify a)))
        genProgEqTypes pa gp
            | size gp < 1 = return . allowIfNoLoopNeeded gp . Just $ genId pa
            | size gp == 1 = allowIfNoLoopNeeded gp <$> Gen.frequency [(9, Gen.constant . Just $ arbitraryFn pa pa), (1, Gen.constant . Just $ genPre pa)]
            | otherwise = case pa of
                ProxV ->
                    let (gpl, gpr) = splitBetween gp
                    in chooseAndTry [
                            maybeComp (genProg ProxV ProxV gpl) (genProg ProxV ProxV gpr),
                            maybeComp (genProg ProxV (ProxP ProxV ProxV) gpl) (genProg (ProxP ProxV ProxV) ProxV gpr),
                            genLoopD ProxV ProxV gp (Gen.constant (Just $ genId ProxV)) (Gen.constant (Just $ genId ProxV))]
                p@(ProxP a b) ->
                    let (gpl, gpr) = splitBetween gp
                    in chooseAndTry [
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
                            maybePar (genProg a a gpl) (genDecoupled b b gpr),
                            genLoopD p p gp (Gen.constant (Just $ genId p)) (Gen.constant (Just $ genId p))]
        -- In this case, we cannot generate id, but we can still generate arbitrary functions.
        genProgDiffTypes :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
        genProgDiffTypes pa pb gp
            | size gp < 1 = return Nothing
            | size gp == 1 = return . allowIfNoLoopNeeded gp . Just $ arbitraryFn pa pb
            | otherwise = 
                let (gpl, gpr) = splitBetween gp
                in chooseAndTry [
                        maybeComp (genProg pa pa gpl) (genProg pa pb gpr),
                        maybeComp (genProg pa pb gpl) (genProg pb pb gpr),
                        genLoopD pa pb gp (Gen.constant (Just $ genId pa)) (Gen.constant (Just $ genId pb))]

-- Generate a decoupled program of the arity described by @pa@ and @pb@.
genDecoupled :: (ValidDesc a, ValidDesc b) => PDesc a -> PDesc b -> GenParam -> Gen (Maybe (CFSF a b, SF (Simplify a) (Simplify b)))
genDecoupled pa pb gp =
    case pDescEq pa pb of
        Just HRefl -> genDecoupledEqTypes pa gp
        -- If the input and output are of different types, we can only generate a LoopM or a composition of decoupled programs.
        Nothing -> if size gp < 2 then return Nothing else
            let (gpl, gpr) = splitBetween gp
                gens = gensDecoupledPair pa pb pb gpl gpr
                    ++ gensDecoupledPair pa pa pb gpl gpr
                    ++ [genLoopM pa pb gp]
            in chooseAndTry gens
    where
        -- If the input and output are of the same type, we can generate a pre as a small decoupled program.
        genDecoupledEqTypes :: ValidDesc a => PDesc a -> GenParam -> Gen (Maybe (CFSF a a, SF (Simplify a) (Simplify a)))
        genDecoupledEqTypes pa gp
            | size gp < 1 = return Nothing
            | size gp == 1 = return . allowIfNoLoopNeeded gp . Just $ genPre pa
            | otherwise = case pa of
                ProxV -> 
                    let (gpl, gpr) = splitBetween gp
                        gens = gensDecoupledPair ProxV ProxV ProxV gpl gpr
                            ++ gensDecoupledPair ProxV (ProxP ProxV ProxV) ProxV gpl gpr
                            ++ [genLoopM ProxV ProxV gp]
                    in chooseAndTry gens
                p@(ProxP a b) ->
                    let (gpl, gpr) = splitBetween gp
                        gensC = gensDecoupledPair p p p gpl gpr ++
                                gensDecoupledPair p a p gpl gpr ++
                                gensDecoupledPair p b p gpl gpr ++
                                gensDecoupledPair p (ProxP p ProxV) p gpl gpr ++
                                gensDecoupledPair p (ProxP ProxV p) p gpl gpr ++
                                [genLoopM p p gp] ++
                                genDecouplingWithinLoopD a b gp
                        gensP = maybePar (genDecoupled a a gpl) (genDecoupled b b gpr)
                    in chooseAndTry $ gensP : gensC
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
                        (maybePar (genDecoupled pa pa gp6) (Gen.constant $ Just $ genId pb)) (Gen.constant (Just $ genId (ProxP pa pb)))),
                -- LoopD with (f *** Pre) right tightenable >>> (dec *** nodec)
                -- LoopD...
                maybeComp (genLoopD (ProxP pa pb) (ProxP pa pb) gp3
                    -- with right tightenable nodec *** dec
                    (Gen.constant (Just $ genId (ProxP pa pb))) (maybePar (Gen.constant $ Just $ genId pa) (genDecoupled pb pb gp4)))
                    -- dec *** nodec
                    (maybePar (genDecoupled pa pa gp5) (genProg pb pb gp6))
                ]

-- A decoupled SF can consist of f >>> g, where either (or both) f or g are decoupled.
gensDecoupledPair :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
    PDesc a -> PDesc b -> PDesc c -> GenParam -> GenParam -> [Gen (Maybe (CFSF a c, SF (Simplify a) (Simplify c)))]
gensDecoupledPair pa pb pc gpl gpr = [
        maybeComp (genProg pa pb gpl) (genDecoupled pb pc gpr),
        maybeComp (genDecoupled pa pb gpl) (genProg pb pc gpr),
        maybeComp (genDecoupled pa pb gpl) (genDecoupled pb pc gpr)
    ]

-- GENERATE FUNCTIONS OF ARBITRARY ARITY
-- We do this by transforming every input into a single value, and then duplicating that value over every output.

{-# INLINE arbitraryFn #-}
arbitraryFn :: (ValidDesc d, ValidDesc d') => PDesc d -> PDesc d' ->
    (CFSF d d', SF (Simplify d) (Simplify d'))
arbitraryFn d d' = let
    (cfsfl, sfl) = reduce d
    (cfsfr, sfr) = duplicate d'
    in (Single . Arr $! cfsfr . cfsfl, A.arr $! sfr . sfl)

{-# INLINE reduce #-}
reduce :: PDesc d -> (Val d -> Val (V Double), Simplify d -> Double)
reduce ProxV = (\(One x) -> One (x/1.1), (/1.1))
reduce (ProxP a b) =
    let
        (cfsfl, sfl) = reduce a
        (cfsfr, sfr) = reduce b
    in (\(Pair x y) ->
            let One x' = cfsfl x
                One y' = cfsfr y
            in One $ (x'/1.1) + (y'/1.1),
        \(x,y) -> (sfl x / 1.1) + (sfr y / 1.1))

{-# INLINE duplicate #-}
duplicate :: PDesc d -> (Val (V Double) -> Val d, Double -> Simplify d)
duplicate ProxV = (\(One x) -> One (x*1.1), (*1.1))
duplicate (ProxP a b) =
    let
        (cfsfl, sfl) = duplicate a
        (cfsfr, sfr) = duplicate b
    in (\x -> Pair (cfsfl x) (cfsfr x), \x -> (sfl x, sfr x))

genPre :: ValidDesc d => PDesc d -> (CFSF d d, SF (Simplify d) (Simplify d))
genPre pd = let (zl, zr) = genOne pd in (pre_ zl, iPre zr)

genId :: ValidDesc d => PDesc d -> (CFSF d d, SF (Simplify d) (Simplify d))
genId _ = (id_, C.id)

genOne :: PDesc a -> (Val a, Simplify a)
genOne ProxV = (One 1, 1)
genOne (ProxP a b) =
    let (cfsfl, sfl) = genOne a
        (cfsfr, sfr) = genOne b
    in (Pair cfsfl cfsfr, (sfl, sfr))