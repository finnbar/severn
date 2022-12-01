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

transformLoopD :: LoopBox a b -> Maybe (ANF a b)
transformLoopD _ = Nothing

-- If this is in the form of a LoopD, make it so.
-- Also apply left/right tightening.
isLoopD :: LoopBox a b -> Maybe (ANF a b)
isLoopD (LB anf) = case initLast anf of
    Left (f :***: g) ->
        asDecoupled g >>= Just . tightening (Single f *** id_)
    Right (IL ss (f :***: g)) ->
        asDecoupled g >>= Just . tightening (ss :>>>: (Single f *** id_))
    _ -> Nothing

-- Apply left/right tightening to the ANF.
tightening :: ANF (P a c) (P b d) -> Decoupled d c -> ANF a b
tightening = undefined

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