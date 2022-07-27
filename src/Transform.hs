{-# LANGUAGE ScopedTypeVariables #-}

module Transform where

import ArrowNF
import Data.Maybe (fromMaybe)
import Control.Applicative (Alternative((<|>)))
import Debug.Trace

data ALP a b where
    LoopPre :: Val c -> NoLoop (P a c) (P b c) -> ALP a b
    WithoutLoopPre :: NoLoop a b -> ALP a b

runALP :: ALP a b -> Val a -> (Val b, ALP a b)
runALP (WithoutLoopPre f) a =
    let (b, f') = runNoLoop f a
    in (b, WithoutLoopPre f')
runALP (LoopPre i f) a =
    let (Pair b c, f') = runNoLoop f (Pair a i)
    in (b, LoopPre c f')

instance Show (ALP a b) where
    show (WithoutLoopPre f) = show f
    show (LoopPre c f) = "LoopPre " ++ show f

transform :: ANF a b -> ALP a b
transform (WithoutLoop f) = WithoutLoopPre f
transform (Loop f) = transform' (WithoutComp Id) f

-- This _simulates_ a Squish between the two arguments - aka the network we
-- work with is actually:
-- second preS >>> Squish >>> second postS
-- but to avoid difficulties with pair types, we just work with preS and postS.
transform' :: NoLoop d (P b c) -> NoLoop (P a c) d -> ALP a b
transform' preS postS@(WithoutComp p) = fromMaybe (rightSlide preS postS) $
    checkSuccess preS (WithoutComp Id) p
transform' preS postS@(pS :>>>: p) = fromMaybe (rightSlide preS postS) $
    checkSuccess preS pS p

checkSuccess :: forall a b c d e.
    NoLoop d (P b c) -> NoLoop (P a c) e -> NoComp e d -> Maybe (ALP a b)
checkSuccess preS postS p = fullPre p <|> leftUnsquish p <|> rightUnsquish p
    where
        fullPre :: NoComp e d -> Maybe (ALP a b)
        fullPre p = do
            (i, p') <- extractPre p
            return $
                LoopPre i $ ((id_ `par` preS) :>>>: Squish) `comp` (id_ `par` (postS :>>>: p'))
        leftUnsquish :: NoComp e d -> Maybe (ALP a b)
        leftUnsquish (x :***: p) = do
            (i, p') <- extractPre p
            (postSL, postSR) <- unpar postS
            return $
                LoopPre i $ ((postSL :>>>: x) `par` id_) `comp` preS `comp` (id_ `par` (postSR :>>>: p'))
        leftUnsquish _ = Nothing
        rightUnsquish :: NoComp e d -> Maybe (ALP a b)
        rightUnsquish (x :***: p) = do
            (i, p') <- extractPre p
            (preSL, preSR) <- unpar preS
            return $
                LoopPre i $ (id_ `par` preSR) `comp` postS `comp` ((WithoutComp x `comp` preSL) `par` WithoutComp p')
        rightUnsquish _ = Nothing

unpar :: NoLoop (P a b) (P c d) -> Maybe (NoLoop a c, NoLoop b d)
unpar (WithoutComp (x :***: y)) = Just (WithoutComp x, WithoutComp y)
unpar (WithoutComp Id) = Just (WithoutComp Id, WithoutComp Id)
unpar (f :>>>: (x :***: y)) = do
    (l, r) <- unpar f
    return (l :>>>: x, r :>>>: y)
unpar (f :>>>: Id) = unpar f
unpar _ = Nothing

extractPre :: NoComp a b -> Maybe (Val b, NoComp a b)
extractPre (Pre i) = Just (i, Id)
extractPre (a :***: b) = do
    (l, Id) <- extractPre a
    (r, Id) <- extractPre b
    return (Pair l r, Id)
extractPre _ = Nothing

rightSlide :: NoLoop d (P b c) -> NoLoop (P a c) d -> ALP a b
rightSlide preS postS =
    case swapCombinatorsInwards postS of
        -- Notably, we _can_ slide further, but only one step further (have the
        -- Squish at the end), and there is no way for that to be a success.
        WithoutComp _ -> error "Cannot slide any further!"
        (pS :>>>: p) -> doRightSlide preS pS p

-- To perform a slide, we first attempt to split the tail of postS into two -
-- noslide :>>>: slide.
-- This is necessary for the following transformation:
-- ... >>> (pre v *** id) >>> (f *** pre v) ==> (f *** id) >>> ... >>> (pre v *** pre v)
-- which may be necessary to reach a success condition.
-- Once we've done that, we move `slide` into `preS` and keep `noslide` around.
doRightSlide :: NoLoop d (P b c) -> NoLoop (P a c) e -> NoComp e d -> ALP a b
doRightSlide preS postS@(WithoutComp p') p =
    case compTwoCompose $ keepPres p' p of
        WithoutComp slide -> transform' (WithoutComp slide `comp` preS) postS
        noslide :>>>: slide -> transform' (WithoutComp slide `comp` preS) (postS `comp` noslide)
doRightSlide preS postS@(pS :>>>: p') p =
    case compTwoCompose $ keepPres p' p of
        WithoutComp slide -> transform' (WithoutComp slide `comp` preS) postS
        noslide :>>>: slide -> transform' (WithoutComp slide `comp` preS) (postS `comp` noslide)

-- Push combinators (Assoc, Cossa, etc.) as far to the left as possible.
swapCombinatorsInwards :: NoLoop a b -> NoLoop a b
swapCombinatorsInwards (WithoutComp f) = WithoutComp f
swapCombinatorsInwards i@(WithoutComp f :>>>: g) = fromMaybe i (trySwap f g)
swapCombinatorsInwards i@((f :>>>: g) :>>>: h) = case trySwap g h of
    Just c -> swapCombinatorsInwards (f `comp` c)
    Nothing -> swapCombinatorsInwards (f :>>>: g) :>>>: h

-- Attempt to swap Assoc etc inwards. Returns Nothing if no change was made.
-- TODO: Try to make _routers_ which generalise Assoc etc. For now we'll stick with the combinators.
-- If I do this, then I can split up Ids here to simplify pattern matching, rather
-- than trying to permanently split up Id.
trySwap :: NoComp a b -> NoComp b c -> Maybe (NoLoop a c)
-- Assoc :: NoComp (P (P a b) c) (P a (P b c))
trySwap ((i :***: j) :***: k) Assoc = Just $ lift_ Assoc `comp` (lift_ i `par` (lift_ j `par` lift_ k))
trySwap (Id :***: k) Assoc = Just $ lift_ Assoc `comp` (id_ `par` (id_ `par` lift_ k))
-- Cossa :: NoComp (P a (P b c)) (P (P a b) c)
trySwap (i :***: (j :***: k)) Cossa = Just $ lift_ Cossa `comp` ((lift_ i `par` lift_ j) `par` lift_ k)
trySwap (i :***: Id) Cossa = Just $ lift_ Cossa `comp` ((lift_ i `par` id_) `par` id_)
-- Juggle :: NoComp (P (P a b) c) (P (P a c) b)
trySwap ((i :***: j) :***: k) Juggle = Just $ lift_ Juggle `comp` ((lift_ i `par` lift_ k) `par` lift_ j)
trySwap (Id :***: k) Juggle = Just $ lift_ Juggle `comp` ((id_ `par` lift_ k) `par` id_)
-- Distribute :: NoComp (P (P a b) (P c d)) (P (P a c) (P b d))
trySwap ((i :***: j) :***: (k :***: l)) Distribute = Just $ lift_ Distribute `comp` ((lift_ i `par` lift_ k) `par` (lift_ j `par` lift_ l))
trySwap (Id :***: (k :***: l)) Distribute = Just $ lift_ Distribute `comp` ((id_ `par` lift_ k) `par` (id_ `par` lift_ l))
trySwap ((i :***: j) :***: Id) Distribute = Just $ lift_ Distribute `comp` ((lift_ i `par` id_) `par` (lift_ j `par` id_))
-- Squish :: NoComp (P a (P b c)) (P b (P a c))
trySwap (i :***: (j :***: k)) Squish = Just $ lift_ Squish `comp` (lift_ j `par` (lift_ i `par` lift_ k))
trySwap (i :***: Id) Squish = Just $ lift_ Squish `comp` (id_ `par` (lift_ i `par` id_))
trySwap _ _ = Nothing

-- This replaces a single NoComp with a composition of two parts:
-- don't slide :>>>: slide
-- This means that if we have an incomplete Pre, we keep it just in case it
-- merges in with the next rightmost part of the program.
-- The first argument is the element before this one - this avoids an infinite
-- loop by only allowing partial slide (ones where we keep Pre back) if it
-- is possible for these Pre to merge with the previous element.
keepPres :: NoComp a b -> NoComp b c -> CompTwo b c
-- If you see a Pre, keep it.
keepPres _ (Pre i) = C2 (Pre i) Id
-- If you see a pair, and there's a pair behind this, keep each element of the pair.
keepPres (a :***: b) (c :***: d) = compTwoPar (keepPres a c) (keepPres b d)
-- Otherwise, drop the element (allow it to be rotated).
keepPres _ x = C2 Id x