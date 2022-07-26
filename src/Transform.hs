{-# LANGUAGE DataKinds, ScopedTypeVariables #-}

module Transform where

import ArrowNF

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
-- Perform a Squish first, to ease sliding.
transform (Loop f) =
    transform' $ WithoutComp Squish `comp` (id_ `par` f)

transform' :: NoLoop (P a c) (P b c) -> ALP a b
transform' (WithoutComp f) = case f of
    -- Reached a success condition. (1)
    currL :***: currR -> case extractPre currR of
        Just (i, currR') -> LoopPre i (WithoutComp (currL :***: currR'))
        Nothing -> error "Cannot convert into loopPre."
    -- TODO: check for unsquish
    -- No rules can be applied.
    _ -> error "Cannot convert into loopPre."
-- TODO: check for unsquish
transform' (prev :>>>: curr) = compTransformRight prev curr

-- Check for the success condition on squished ANFs
unsquish :: NoLoop (P a c) (P b c) -> Maybe (ALP a b)
unsquish (WithoutComp _) = Nothing
unsquish (f :>>>: (currL :***: (currR1 :***: currR2))) = do
    -- If we have a pre in the bottom half of the bottom right
    (i, currR2') <- extractPre currR2
    -- Get the post-Squish tail, splitting it into top and bottom
    undefined
unsquish (_ :>>>: _) = Nothing

compTransformRight :: NoLoop (P a c) d -> NoComp d (P b c) -> ALP a b
-- Check if there is a pre in the bottom right - if so, replace it with Id
-- and we're done.
compTransformRight prev curr@(currL :***: currR) = case extractPre currR of
    Just (i, currR') -> LoopPre i (prev :>>>: (currL :***: currR'))
    Nothing -> rightSlide prev curr
compTransformRight prev curr = rightSlide prev curr

extractPre :: NoComp a b -> Maybe (Val b, NoComp a b)
extractPre (Pre i) = Just (i, Id)
extractPre (a :***: b) = do
    (l, Id) <- extractPre a
    (r, Id) <- extractPre b
    return (Pair l r, Id)
extractPre _ = Nothing

rightSlide :: forall a b c d. NoLoop (P a c) d -> NoComp d (P b c) -> ALP a b
-- If you can perform a right slide, do so.
rightSlide prev (currL :***: currR) =
    case prev of
        -- Use right sliding (loop (a >>> (b *** c)) = loop ((id *** c) >>> a >>> (b *** id))). (3)
        -- Sometimes we perform a _partial slide_ - see @partialRightSlide@ for details.
        WithoutComp (_ :***: prevR) -> partialRightSlide currL currR prevR prev
        (_ :>>>: (_ :***: prevR)) -> partialRightSlide currL currR prevR prev
        -- If we don't have a :***:, first try `attemptSwapRight` to move Assoc etc outwards
        ((rest :>>>: p) :>>>: prev') -> case attemptSwapRight p prev' of
            Just c -> rightSlide (rest `comp` c) (currL :***: currR)
            Nothing -> doSlide prev currL currR
        (WithoutComp p :>>>: prev') -> case attemptSwapRight p prev' of
            Just c -> rightSlide c (currL :***: currR)
            _ -> doSlide prev currL currR
        _ -> doSlide prev currL currR
    where
        doSlide :: NoLoop (P a c) (P e f) -> NoComp e b -> NoComp f c -> ALP a b
        doSlide p cL cR = transform' $ ((id_ `par` lift_ cR) `comp` p) `comp` (lift_ cL `par` id_)
-- If you cannot perform a right slide, attempt to swap the end of the arrow back one step,
-- hopefully revealing something that can be slid.
rightSlide (prev :>>>: p) curr = case attemptSwapRight p curr of
    Just c -> transform' (prev `comp` c)
    Nothing -> error "got stuck!"
rightSlide (WithoutComp p) curr = case attemptSwapRight p curr of
    Just c -> transform' c
    Nothing -> error "got stuck!"

-- Attempt to swap Assoc etc inwards. Returns Nothing if no change was made.
-- TODO: Try to make _routers_ which generalise Assoc etc. For now we'll stick with the combinators.
-- If I do this, then I can split up Ids here to simplify pattern matching, rather
-- than trying to permanently split up Id.
attemptSwapRight :: NoComp a b -> NoComp b c -> Maybe (NoLoop a c)
-- Assoc :: NoComp (P (P a b) c) (P a (P b c))
attemptSwapRight ((i :***: j) :***: k) Assoc = Just $ lift_ Assoc `comp` (lift_ i `par` (lift_ j `par` lift_ k))
attemptSwapRight (Id :***: k) Assoc = Just $ lift_ Assoc `comp` (id_ `par` (id_ `par` lift_ k))
-- Cossa :: NoComp (P a (P b c)) (P (P a b) c)
attemptSwapRight (i :***: (j :***: k)) Cossa = Just $ lift_ Cossa `comp` ((lift_ i `par` lift_ j) `par` lift_ k)
attemptSwapRight (i :***: Id) Cossa = Just $ lift_ Cossa `comp` ((lift_ i `par` id_) `par` id_)
-- Juggle :: NoComp (P (P a b) c) (P (P a c) b)
attemptSwapRight ((i :***: j) :***: k) Juggle = Just $ lift_ Juggle `comp` ((lift_ i `par` lift_ k) `par` lift_ j)
attemptSwapRight (Id :***: k) Juggle = Just $ lift_ Juggle `comp` ((id_ `par` lift_ k) `par` id_)
-- Distribute :: NoComp (P (P a b) (P c d)) (P (P a c) (P b d))
attemptSwapRight ((i :***: j) :***: (k :***: l)) Distribute = Just $ lift_ Distribute `comp` ((lift_ i `par` lift_ k) `par` (lift_ j `par` lift_ l))
attemptSwapRight (Id :***: (k :***: l)) Distribute = Just $ lift_ Distribute `comp` ((id_ `par` lift_ k) `par` (id_ `par` lift_ l))
attemptSwapRight ((i :***: j) :***: Id) Distribute = Just $ lift_ Distribute `comp` ((lift_ i `par` id_) `par` (lift_ j `par` id_))
-- Squish :: NoComp (P a (P b c)) (P b (P a c))
attemptSwapRight (i :***: (j :***: k)) Squish = Just $ lift_ Squish `comp` (lift_ j `par` (lift_ i `par` lift_ k))
attemptSwapRight (i :***: Id) Squish = Just $ lift_ Squish `comp` (id_ `par` (lift_ i `par` id_))
attemptSwapRight _ _ = Nothing

-- This performs a _partial slide_. This means that we slide everything using right sliding,
-- _except_ for any `pre` if they could be merged into the previous part of the program.
-- (`keepPres` has more detail on this.)
-- This is necessary for solving programs written like:
-- ... >>> second ((pre v *** id) >>> (f *** pre v))
-- which would be solved by sliding only the f to the other side, i.e.:
-- second (first f) >>> ... >>> second (pre (v,v))
-- To do this, we split the term we are about to slide (currR) into a part to slide (slide)
-- and a part to not slide (noslide), and assemble the new Loop accordingly.
partialRightSlide :: NoComp b c -> NoComp b' c' -> NoComp a' b' -> NoLoop (P a c') (P b b') -> ALP a c
partialRightSlide currL currR prevR prev = case compTwoCompose $ keepPres prevR currR of
    WithoutComp currR' -> transform' $ ((id_ `par` lift_ currR') `comp` prev) `comp` (lift_ currL `par` id_)
    noslide :>>>: slide -> transform' $ ((id_ `par` lift_ slide) `comp` prev) `comp` (lift_ currL `par` noslide)

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
