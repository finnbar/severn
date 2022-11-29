{-# LANGUAGE FlexibleContexts #-}

module TransformRight where

import ArrowNF

import Control.Applicative ((<|>))

-- Code for transforming loops solvable with right sliding.

-- TODO: am I certain that there's no nice way to do this with squash only?
-- Is there some kind of way to unslide stuff if we've got a pre in the right place?
-- That being said, this needs to be explainable.

-- TODO: add combinator stuff and right crunch up here.
transformRight :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d) =>
    NoLoop (P a c) d -> NoLoop d (P b c) -> Maybe (ALP a b)
transformRight preS (WithoutComp p) = checkSuccess preS id_ p
transformRight preS (postS :>>>: p) =
    checkSuccess preS postS p <|> rightSlide preS postS p

checkSuccess :: (ValidDesc a, ValidDesc d) =>
    NoLoop (P a c) d -> NoLoop d e -> NoComp e (P b c) -> Maybe (ALP a b)
checkSuccess preS postS (x :***: p) = do
    (i, p') <- extractPre p
    return $
        LoopPre i $ preS `comp` (postS :>>>: (x :***: p'))
checkSuccess _ _ _ = Nothing

extractPre :: NoComp a b -> Maybe (Val b, NoComp a b)
extractPre (Pre i) = Just (i, Id)
extractPre (a :***: b) = do
    (l, Id) <- extractPre a
    (r, Id) <- extractPre b
    return (Pair l r, Id)
extractPre _ = Nothing

rightSlide :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d) =>
    NoLoop (P a c) d -> NoLoop d e -> NoComp e (P b c) -> Maybe (ALP a b)
rightSlide preS postS (p :***: s) =
    case postS of
        WithoutComp (psl :***: psr) -> partialSlide preS (WithoutComp Id) psl psr p s
        (pS :>>>: (psl :***: psr)) -> partialSlide preS pS psl psr p s
        _ -> transformRight (WithoutComp (Id :***: s) `comp` preS) (postS `comp` WithoutComp (p :***: Id))
rightSlide _ _ _ = Nothing

partialSlide :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d, ValidDesc e, ValidDesc f, ValidDesc g, ValidDesc h) =>
    NoLoop (P a c) d -> NoLoop d (P e f) ->
    NoComp e g -> NoComp f h -> NoComp g b -> NoComp h c -> Maybe (ALP a b)
partialSlide preS pS psl psr p s = case compTwoCompose $ keepPres psr s of
    noslide :>>>: slide -> transformRight ((id_ `par` WithoutComp slide) `comp` preS) (pS `comp` WithoutComp (psl :***: psr) `comp` (WithoutComp p `par` noslide))
    WithoutComp slide -> transformRight ((id_ `par` WithoutComp slide) `comp` preS) (pS `comp` WithoutComp (psl :***: psr) `comp` (WithoutComp p `par` id_))

separatePre :: (ValidDesc b, ValidDesc c) => NoLoop a b -> NoComp b c -> NoLoop b c
separatePre (WithoutComp p') p = compTwoCompose $ keepPres p' p
separatePre (xs :>>>: p') p = compTwoCompose $ keepPres p' p

-- Push combinators (Assoc, Cossa, etc.) as far to the left as possible.
swapCombinatorsInwards :: (ValidDesc a, ValidDesc b) => NoLoop a b -> NoLoop a b
swapCombinatorsInwards (WithoutComp nl) = WithoutComp nl
swapCombinatorsInwards nl@(WithoutComp f :>>>: g) = case swapHelp nl of
    (nl', True) -> swapCombinatorsInwards nl'
    (nl', False) -> nl'
swapCombinatorsInwards ((f :>>>: g) :>>>: h) = case swapHelp (swapCombinatorsInwards (f :>>>: g) :>>>: h) of
    (nl', True) -> swapCombinatorsInwards nl'
    (nl', False) -> nl'

-- The Bool represents whether any change has been made in this pass.
swapHelp :: (ValidDesc a, ValidDesc b) => NoLoop a b -> (NoLoop a b, Bool)
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
pullThrough :: (ValidDesc a, ValidDesc b, ValidDesc c) => NoComp a b -> NoComp b c -> Maybe (NoLoop a c)
pullThrough exp Assoc = pullThroughAssoc exp
pullThrough exp Cossa = pullThroughCossa exp
pullThrough exp Juggle = pullThroughJuggle exp
pullThrough exp Distribute = pullThroughDistribute exp
pullThrough exp Squish = pullThroughSquish exp
pullThrough _ _ = Nothing

pullThroughAssoc :: (ValidDesc a, ValidDesc d, ValidDesc e) => NoComp a (P (P d e) f) -> Maybe (NoLoop a (P d (P e f)))
pullThroughAssoc ((i :***: j) :***: k) = Just $ lift_ Assoc `comp` (lift_ i `par` (lift_ j `par` lift_ k))
pullThroughAssoc (Id :***: k) = Just $ lift_ Assoc `comp` (id_ `par` (id_ `par` lift_ k))
-- This prevents an infinite loop in the next rule - since if you set k = Id, you get an identical result.
pullThroughAssoc (x :***: Id) = Nothing
pullThroughAssoc (x :***: k) = Just $ lift_ (x :***: Id) `comp` lift_ Assoc `comp` (id_ `par` (id_ `par` lift_ k))
pullThroughAssoc _ = Nothing

pullThroughCossa :: (ValidDesc a, ValidDesc d, ValidDesc e, ValidDesc f) => NoComp a (P d (P e f)) -> Maybe (NoLoop a (P (P d e) f))
pullThroughCossa (i :***: (j :***: k)) = Just $ lift_ Cossa `comp` ((lift_ i `par` lift_ j) `par` lift_ k)
pullThroughCossa (i :***: Id) = Just $ lift_ Cossa `comp` ((lift_ i `par` id_) `par` id_)
-- Set i = Id in the next rule and you get an identical result.
pullThroughCossa (Id :***: x) = Nothing
pullThroughCossa (i :***: x) = Just $ lift_ (Id :***: x) `comp` lift_ Cossa `comp` ((lift_ i `par` id_) `par` id_)
pullThroughCossa _ = Nothing

pullThroughJuggle :: (ValidDesc a, ValidDesc d, ValidDesc e) => NoComp a (P (P d e) f) -> Maybe (NoLoop a (P (P d f) e))
pullThroughJuggle ((i :***: j) :***: k) = Just $ lift_ Juggle `comp` ((lift_ i `par` lift_ k) `par` lift_ j)
pullThroughJuggle (Id :***: k) = Just $ lift_ Juggle `comp` ((id_ `par` lift_ k) `par` id_)
-- Set k = Id in the next rule and you get an identical result.
pullThroughJuggle (x :***: Id) = Nothing
pullThroughJuggle (x :***: k) = Just $ lift_ (x :***: Id) `comp` lift_ Juggle `comp` ((id_ `par` lift_ k) `par` id_)
pullThroughJuggle _ = Nothing

pullThroughDistribute :: (ValidDesc a, ValidDesc d, ValidDesc e, ValidDesc f, ValidDesc g) => NoComp a (P (P d e) (P f g)) -> Maybe (NoLoop a (P (P d f) (P e g)))
pullThroughDistribute ((i :***: j) :***: (k :***: l)) = Just $ lift_ Distribute `comp` ((lift_ i `par` lift_ k) `par` (lift_ j `par` lift_ l))
pullThroughDistribute (Id :***: (k :***: l)) = Just $ lift_ Distribute `comp` ((id_ `par` lift_ k) `par` (id_ `par` lift_ l))
pullThroughDistribute ((i :***: j) :***: Id) = Just $ lift_ Distribute `comp` ((lift_ i `par` id_) `par` (lift_ j `par` id_))
pullThroughDistribute _ = Nothing

pullThroughSquish :: (ValidDesc a, ValidDesc d, ValidDesc e, ValidDesc f) => NoComp a (P d (P e f)) -> Maybe (NoLoop a (P e (P d f)))
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
keepPres :: (ValidDesc b, ValidDesc c) => NoComp a b -> NoComp b c -> CompTwo b c
-- If you see a Pre, keep it.
keepPres _ (Pre i) = C2 (Pre i) Id
-- If you see a pair, and there's a pair behind this, keep each element of the pair.
keepPres (a :***: b) (c :***: d) = compTwoPar (keepPres a c) (keepPres b d)
-- Otherwise, drop the element (allow it to be rotated).
keepPres _ x = C2 Id x