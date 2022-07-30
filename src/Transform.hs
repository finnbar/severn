{-# LANGUAGE ScopedTypeVariables #-}

module Transform where

import ArrowNF
import Run
import Data.Maybe (fromMaybe)
import Control.Applicative (Alternative((<|>)))
import Debug.Trace

transform :: ANF a b -> ALP a b
transform (WithoutLoop f) = WithoutLoopPre f
transform (Loop f) = transform' (WithoutComp Id) f

-- This _simulates_ a Squish between the two arguments - aka the network we
-- work with is actually:
-- second preS >>> Squish >>> second postS
-- but to avoid difficulties with pair types, we just work with preS and postS.
transform' :: NoLoop d (P b c) -> NoLoop (P a c) d -> ALP a b
transform' preS postS = case {-traceShowId $-} swapCombinatorsInwards postS of
    postS'@(WithoutComp p) -> fromMaybe (rightSlide preS postS') $
        checkSuccess preS (WithoutComp Id) p
    postS'@(pS :>>>: p) -> fromMaybe (rightSlide preS postS') $
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
rightSlide preS (WithoutComp _) = error "Cannot slide any further!"
rightSlide preS (pS :>>>: p) = doRightSlide preS pS p

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

-- Extended algorithm, in an attempt to correctly solve without worry.
-- NOTE: if we ever slide something large across, we know that we can no longer get left unsquish -
-- therefore we can aim to slide combinators across.
-- See my notes - I expect we probably need to simplify rather than trying to solve in one pass.
doRightSlide' :: NoLoop d (P b c) -> NoLoop (P a c) e -> NoComp e d -> ALP a b
doRightSlide' preS postS p = if not $ hasPre p then
    -- If there is no Pre within p, then slide as normal - we have nothing to lose.
    transform' (WithoutComp p `comp` preS) postS
    -- If there is a Pre, then we have to try and keep it around.
    -- First, try to split p into a part containing Pres, and a part containing non-Pres.
    -- If we can do that, then slide the non-Pre part.
    else case separatePre postS p of
        noslide :>>>: slide -> transform' (WithoutComp slide `comp` preS) (postS `comp` noslide)
        WithoutComp p' -> undefined

hasPre :: NoComp a b -> Bool
hasPre (Pre i) = True
hasPre (a :***: b) = hasPre a || hasPre b
hasPre _ = False

separatePre :: NoLoop a b -> NoComp b c -> NoLoop b c
separatePre (WithoutComp p') p = compTwoCompose $ keepPres p' p
separatePre (xs :>>>: p') p = compTwoCompose $ keepPres p' p

-- Push combinators (Assoc, Cossa, etc.) as far to the left as possible.
-- TODO: This isn't entirely working.
-- Also when a solution is left sliding, we have a whole host of other problems.
swapCombinatorsInwards :: NoLoop a b -> NoLoop a b
swapCombinatorsInwards (WithoutComp nl) = WithoutComp nl
swapCombinatorsInwards nl@(WithoutComp f :>>>: g) = case swapHelp nl of
    (nl', True) -> swapCombinatorsInwards nl'
    (nl', False) -> nl'
swapCombinatorsInwards ((f :>>>: g) :>>>: h) = case swapHelp (swapCombinatorsInwards (f :>>>: g) :>>>: h) of
    (nl', True) -> swapCombinatorsInwards nl'
    (nl', False) -> nl'

-- The Bool represents whether any change has been made in this pass.
swapHelp :: NoLoop a b -> (NoLoop a b, Bool)
swapHelp (WithoutComp f) = (WithoutComp f, False)
swapHelp (WithoutComp f :>>>: g) = case pullThrough f g of
    Nothing -> (WithoutComp f `comp` WithoutComp g, False)
    Just c -> (c, True)
swapHelp ((f :>>>: g) :>>>: h) = case pullThrough g h of
    Nothing -> let (fg, b) = swapHelp (f `comp` WithoutComp g) in (fg `comp` WithoutComp h, b)
    Just (WithoutComp c) -> let (fg, _) = swapHelp f in (fg `comp` WithoutComp c, True)
    Just (c :>>>: c') -> let (fg, _) = swapHelp (f `comp` c) in (fg `comp` WithoutComp c', True)

-- @pullThrough@ attempts to pull parts of the program through a combinator like Assoc
-- e.g. if we have (Arr2 :***: Pre) >>> Assoc, we can pull the Pre through:
-- (Arr2 :***: Id) >>> Assoc >>> (Id :***: Pre)
-- and then the new ending part can possibly be pulled through more combinators.
-- TODO: Try to make _routers_ which generalise Assoc etc. For now we'll stick with the combinators.
pullThrough :: NoComp a b -> NoComp b c -> Maybe (NoLoop a c)
pullThrough exp Assoc = pullThroughAssoc exp
pullThrough exp Cossa = pullThroughCossa exp
pullThrough exp Juggle = pullThroughJuggle exp
pullThrough exp Distribute = pullThroughDistribute exp
pullThrough exp Squish = pullThroughSquish exp
pullThrough _ _ = Nothing

pullThroughAssoc :: NoComp a (P (P d e) f) -> Maybe (NoLoop a (P d (P e f)))
pullThroughAssoc ((i :***: j) :***: k) = Just $ lift_ Assoc `comp` (lift_ i `par` (lift_ j `par` lift_ k))
pullThroughAssoc (Id :***: k) = Just $ lift_ Assoc `comp` (id_ `par` (id_ `par` lift_ k))
-- This prevents an infinite loop in the next rule - since if you set k = Id, you get an identical result.
pullThroughAssoc (x :***: Id) = Nothing
pullThroughAssoc (x :***: k) = Just $ lift_ (x :***: Id) `comp` lift_ Assoc `comp` (id_ `par` (id_ `par` lift_ k))
pullThroughAssoc _ = Nothing

pullThroughCossa :: NoComp a (P d (P e f)) -> Maybe (NoLoop a (P (P d e) f))
pullThroughCossa (i :***: (j :***: k)) = Just $ lift_ Cossa `comp` ((lift_ i `par` lift_ j) `par` lift_ k)
pullThroughCossa (i :***: Id) = Just $ lift_ Cossa `comp` ((lift_ i `par` id_) `par` id_)
-- Set i = Id in the next rule and you get an identical result.
pullThroughCossa (Id :***: x) = Nothing
pullThroughCossa (i :***: x) = Just $ lift_ (Id :***: x) `comp` lift_ Cossa `comp` ((lift_ i `par` id_) `par` id_)
pullThroughCossa _ = Nothing

pullThroughJuggle :: NoComp a (P (P d e) f) -> Maybe (NoLoop a (P (P d f) e))
pullThroughJuggle ((i :***: j) :***: k) = Just $ lift_ Juggle `comp` ((lift_ i `par` lift_ k) `par` lift_ j)
pullThroughJuggle (Id :***: k) = Just $ lift_ Juggle `comp` ((id_ `par` lift_ k) `par` id_)
-- Set k = Id in the next rule and you get an identical result.
pullThroughJuggle (x :***: Id) = Nothing
pullThroughJuggle (x :***: k) = Just $ lift_ (x :***: Id) `comp` lift_ Juggle `comp` ((id_ `par` lift_ k) `par` id_)
pullThroughJuggle _ = Nothing

pullThroughDistribute :: NoComp a (P (P d e) (P f g)) -> Maybe (NoLoop a (P (P d f) (P e g)))
pullThroughDistribute ((i :***: j) :***: (k :***: l)) = Just $ lift_ Distribute `comp` ((lift_ i `par` lift_ k) `par` (lift_ j `par` lift_ l))
pullThroughDistribute (Id :***: (k :***: l)) = Just $ lift_ Distribute `comp` ((id_ `par` lift_ k) `par` (id_ `par` lift_ l))
pullThroughDistribute ((i :***: j) :***: Id) = Just $ lift_ Distribute `comp` ((lift_ i `par` id_) `par` (lift_ j `par` id_))
pullThroughDistribute _ = Nothing

pullThroughSquish :: NoComp a (P d (P e f)) -> Maybe (NoLoop a (P e (P d f)))
pullThroughSquish (i :***: (j :***: k)) = Just $ lift_ Squish `comp` (lift_ j `par` (lift_ i `par` lift_ k))
pullThroughSquish (i :***: Id) = Just $ lift_ Squish `comp` (id_ `par` (lift_ i `par` id_))
-- Set i = Id in the next rule and you get an identical result.
pullThroughSquish (Id :***: x) = Nothing
pullThroughSquish (i :***: x) = Just $ lift_ (Id :***: x) `comp` lift_ Squish `comp` (id_ `par` (lift_ i `par` id_))
pullThroughSquish _ = Nothing

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