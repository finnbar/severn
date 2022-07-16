module Transform where

import ArrowNF
import Helpers

-- BIG TODO: might be more helpful to have a graph representation?
-- That sounds like a problem of statically ordering laziness at compile time.
-- The challenge is working with `arr`s that reroute data (so may be fine to execute bc laziness).
-- I have no idea how to differentiate between them and normal `arr`s.
-- Generalised arrows _might_ help?
-- Might be best to provide specialised Arr for these combinators, so maybe Assoc etc., which can be
-- reasoned about or split up.

data ALP a b where
    LoopPre :: c -> NoLoop (a,c) (b,c) -> ALP a b
    WithoutLoopPre :: NoLoop a b -> ALP a b

runALP :: ALP a b -> a -> (b, ALP a b)
runALP (WithoutLoopPre f) a =
    let (b, f') = runNoLoop f a
    in (b, WithoutLoopPre f')
runALP (LoopPre i f) a =
    let ((b,c), f') = runNoLoop f (a,i)
    in (b, LoopPre c f')

instance Show (ALP a b) where
    show (WithoutLoopPre f) = show f
    show (LoopPre c f) = "LoopPre " ++ show f

transform :: ANF a b -> ALP a b
transform (WithoutLoop f) = WithoutLoopPre f
transform (Loop (WithoutComp f)) = case f of
    -- Reached a success condition. (1)
    currL :***: (Pre i) -> LoopPre i (WithoutComp (currL :***: Id))
    -- Product rule then success (pre (i,j) = pre i *** pre j). (2)
    Pre (i,j) -> LoopPre j (WithoutComp (Pre i :***: Id))
    -- No rules can be applied.
    _ -> error "Cannot convert into loopPre."
transform (Loop prog@(prev :>>>: curr)) = case curr of
    currL :***: currR -> case succeeded currL currR of
        -- Reached a success condition. (1)
        Just (res, del) -> LoopPre del (prev :>>>: res)
        -- Use right sliding (loop (a >>> (b *** c)) = loop ((id *** c) >>> a >>> (b *** id))). (3)
        -- Sometimes we perform a _partial slide_ - see @partialSlide@ for details.
        -- NOTE: may have to update these if I do complex stuff with Assoc/Squish.
        Nothing -> case prev of
            WithoutComp (_ :***: prevR) -> transform $ partialSlide currL currR prevR prev
            (_ :>>>: (_ :***: prevR)) -> transform $ partialSlide currL currR prevR prev
            _ -> transform $ Loop $ ((id_ `par` lift_ currR) `comp` prev) `comp` (lift_ currL `par` id_)
    -- Product rule then success. (2)
    Pre (i,j) -> LoopPre j (prev :>>>: (Pre i :***: Id))
    -- TODO: Reverse squash (5)
    -- Left squash. (4)
    _ -> transform $ Loop $ WithoutComp (Arr squish) `comp` (WithoutComp Id `par` prog)

-- This performs a _partial slide_. This means that we slide everything using right sliding,
-- _except_ for any `pre` if they could be merged into the previous part of the program.
-- (`keepPres` has more detail on this.)
-- This is necessary for solving programs written like:
-- ... >>> second ((pre v *** id) >>> (f *** pre v))
-- which would be solved by sliding only the f to the other side, i.e.:
-- second (first f) >>> ... >>> second (pre (v,v))
-- To do this, we split the term we are about to slide (currR) into a part to slide (slide)
-- and a part to not slide (noslide), and assemble the new Loop accordingly.
partialSlide :: NoComp b c -> NoComp b' c' -> NoComp a' b' -> NoLoop (a, c') (b, b') -> ANF a c
partialSlide currL currR prevR prev = case compTwoCompose $ keepPres prevR currR of
    WithoutComp currR' -> Loop $ ((id_ `par` lift_ currR') `comp` prev) `comp` (lift_ currL `par` id_)
    noslide :>>>: slide -> Loop $ ((id_ `par` lift_ slide) `comp` prev) `comp` (lift_ currL `par` noslide)

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

-- Check if the bottom right element is a Pre of some form.
succeeded :: NoComp a b -> NoComp a' b' -> Maybe (NoComp (a,a') (b,b'), b')
succeeded currL (Pre i) = Just (currL :***: Id, i)
succeeded currL (a :***: b) = case isPre (a :***: b) of
    Just (Pre i) -> Just (currL :***: Id, i)
    _ -> Nothing
succeeded _ _ = Nothing

isPre :: NoComp a b -> Maybe (NoComp a b)
isPre (Pre i) = Just (Pre i)
isPre (a :***: b) = (:***:) <$> isPre a <*> isPre b
isPre _ = Nothing