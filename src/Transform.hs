{-# LANGUAGE ScopedTypeVariables #-}

module Transform where

import ArrowNF
import Data.Maybe (fromJust)
import Control.Applicative (Alternative((<|>)))
import Debug.Trace

data LoopBox a b where
    LB :: ANF (P a c) (P b c) -> LoopBox a b

-- The main transformation algorithm. Tries to transform to LoopM, and then LoopD.
transform :: ANF a b -> ALP a b
transform anf =
    case transformLoopM anf of
        Just alp -> alp
        Nothing -> fromJust $ transformLoopD anf

transformLoopM :: ANF a b -> Maybe (ALP a b)
transformLoopM _ = Nothing

transformLoopD :: ANF a b -> Maybe (ALP a b)
transformLoopD _ = Nothing

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