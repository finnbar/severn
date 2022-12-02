{-# LANGUAGE ScopedTypeVariables #-}

module Transform where

import ArrowNF
import Data.Maybe (fromJust)
import Control.Applicative (Alternative((<|>)))

data LoopBox a b where
    LB :: ANF (P a c) (P b c) -> LoopBox a b

-- Traverse the program to find Loop.
-- ASSUMPTION: We assume that we do not start with any LoopD or LoopM, or at least
-- that no LoopD/LoopM contain Loop.
transform :: ANF a b -> ANF a b
-- If we have a loop, go inside it, then once you're done transform that.
transform (Single (Loop f)) = transformLoop (LB $ transform f)
transform (Single (f :***: g)) = transform (Single f) *** transform (Single g)
transform (Single g) = Single g
-- If we have a composition, transform the elements of the composition.
transform (f :>>>: g) = transform f :>>>: transform g

-- The main transformation algorithm. Tries to transform to LoopM, and then LoopD.
transformLoop :: LoopBox a b -> ANF a b
transformLoop lb =
    case transformLoopM lb of
        Just anf -> anf
        Nothing -> fromJust $ transformLoopD lb

transformLoopM :: LoopBox a b -> Maybe (ANF a b)
transformLoopM _ = Nothing

-- TODO: We now need to implement this.
-- Check if it's done at each step, otherwise slide, fill/extract.
transformLoopD :: LoopBox a b -> Maybe (ANF a b)
transformLoopD _ = Nothing

-- If this is in the form of a LoopD, make it so.
-- Also apply left/right tightening.
isLoopD :: ValidDesc a => LoopBox a b -> Maybe (ANF a b)
isLoopD (LB anf) = case initLast anf of
    Left (f :***: g) ->
        asDecoupled g >>= Just . tightening (Single f *** id_)
    Right (IL ss (f :***: g)) ->
        asDecoupled g >>= Just . tightening (ss :>>>: (Single f *** id_))
    _ -> Nothing

-- Have to do this to allow for reasonable return types.
data Tightening a f where
    TG :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d, ValidDesc e, ValidDesc f) =>
        ANF a b -> ANF (P b d) (P c e) -> ANF c f -> Decoupled e d -> Tightening a f

-- Apply left/right tightening to the ANF.
-- Use left/right fill to aid the process.
tightening :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d)
    => ANF (P a c) (P b d) -> Decoupled d c -> ANF a b
tightening anf dec = tighteningToANF $ leftTighten $ rightTighten (TG id_ anf id_ dec)
    where
        tighteningToANF :: Tightening a b -> ANF a b
        tighteningToANF (TG l anf r dec) =
            l :>>>: Single (LoopD anf dec) :>>>: r
        rightTighten :: Tightening a b -> Tightening a b
        rightTighten (TG l anf r dec) = case initLast anf of
            Right (IL ss (f :***: g)) ->
                rightTighten (TG l (ss :>>>: Single (idNoComp :***: g)) (Single f :>>>: r) dec)
            _ -> TG l anf r dec
        leftTighten :: Tightening a b -> Tightening a b
        leftTighten (TG l anf r dec) = case headTail anf of
            Right (HT (f :***: g) ss) ->
                leftTighten (TG (l :>>>: Single f) (Single (idNoComp :***: g) :>>>: ss) r dec)
            _ -> TG l anf r dec

-- Move all non-ID terms to the left.
leftCrunch :: ANF a b -> ANF a b
leftCrunch anf = case initLast anf of
    Left _ -> anf
    Right (IL an f) -> case initLast an of
        Left _ -> anf
        Right (IL a n) ->
            leftCrunch' a $ leftFill (C2 n f)
    where
        leftCrunch' :: ValidDesc a => ANF a b -> CompTwo b c -> ANF a c
        leftCrunch' a (C2 n' f') = leftCrunch (a :>>>: Single n') :>>>: Single f'

-- Move all non-ID terms to the right.
rightCrunch :: ANF a b -> ANF a b
rightCrunch anf = case headTail anf of
    Left _ -> anf
    Right (HT a nf) -> case headTail nf of
        Left _ -> anf
        Right (HT n f) ->
            rightCrunch' (rightFill (C2 a n)) f
    where
        rightCrunch' :: ValidDesc c => CompTwo a b -> ANF b c -> ANF a c
        rightCrunch' (C2 a' n') f = Single a' :>>>: rightCrunch (Single n' :>>>: f)

-- Apply right extract to the input term, returning a composition
rightExtract :: (ValidDesc a, ValidDesc b) => NoComp a b -> CompTwo a b
rightExtract (Dec d) = C2 (Dec d) idNoComp
rightExtract (f :***: g) = compTwoPar (rightExtract f) (rightExtract g)
rightExtract f = C2 idNoComp f

-- Apply left extract to the input term, returning a composition
leftExtract :: (ValidDesc a, ValidDesc b) => NoComp a b -> CompTwo a b
leftExtract (Dec d) = C2 idNoComp (Dec d)
leftExtract (f :***: g) = compTwoPar (leftExtract f) (leftExtract g)
leftExtract f = C2 f idNoComp

-- Apply right fill to a composition, moving parts of the composition.
rightFill :: CompTwo a b -> CompTwo a b
rightFill (C2 Id f) = C2 f idNoComp
rightFill (C2 (f :***: g) (h :***: i)) =
    compTwoPar (rightFill $ C2 f h) (rightFill $ C2 g i)
rightFill (C2 f g) = C2 f g

-- Apply left fill to a composition, moving parts of the composition.
leftFill :: CompTwo a b -> CompTwo a b
leftFill (C2 Id f) = C2 f idNoComp
leftFill (C2 (f :***: g) (h :***: i)) =
    compTwoPar (leftFill $ C2 f h) (leftFill $ C2 g i)
leftFill (C2 f g) = C2 f g

asDecoupled :: NoComp a b -> Maybe (Decoupled a b)
asDecoupled (Dec d) = Just d
asDecoupled (f :***: g) = do
    fd <- asDecoupled f
    gd <- asDecoupled g
    return $ BothDec fd gd
asDecoupled _ = Nothing

leftSlide :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (LoopBox a b)
leftSlide (LB anf) = case headTail anf of
    -- If there is only one element of the composition, you cannot slide.
    Left _ -> Nothing
    Right (HT s ss) -> case s of
        -- slide s1
        s1 :***: s2 -> Just $ LB $ (Single s1 *** id_) >>> ss >>> (id_ *** Single s2)
        -- impossible to slide
        _ -> Nothing

rightSlide :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (LoopBox a b)
rightSlide (LB anf) = case initLast anf of
    -- If there is only one element of the composition, you cannot slide.
    Left _ -> Nothing
    Right (IL ss s) -> case s of
        --slide s1
        s1 :***: s2 -> Just $ LB $ (id_ *** Single s2) >>> ss >>> (Single s1 *** id_)
        -- impossible to slide
        _ -> Nothing