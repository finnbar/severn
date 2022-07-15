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
    nc :***: (Pre i) -> LoopPre i (WithoutComp (nc :***: Id))
    -- Product rule then success (pre (i,j) = pre i *** pre j). (2)
    Pre (i,j) -> LoopPre j (WithoutComp (Pre i :***: Id))
    -- No rules can be applied.
    _ -> error "Cannot convert into loopPre."
transform (Loop prog@(a :>>>: f)) = case f of
    nc :***: nc' -> case succeeded nc nc' of
        -- Reached a success condition. (1)
        Just (res, del) -> LoopPre del (a :>>>: res)
        -- Use right sliding (loop (a >>> (b *** c)) = loop ((id *** c) >>> a >>> (b *** id))). (3)
        -- `throughComps squashRight` moves all useful information to the right.
        -- TODO: partial slide, e.g. (Pre x *** y) should only slide y.
        Nothing -> transform $ Loop $ ((id_ `par` lift_ nc') `comp` a) `comp` (lift_ nc `par` id_)
    -- Product rule then success. (2)
    Pre (i,j) -> LoopPre j (a :>>>: (Pre i :***: Id))
    -- TODO: Reverse squash (5)
    -- Left squash. (4)
    _ -> transform $ Loop $ WithoutComp (Arr squish) `comp` (WithoutComp Id `par` prog)

succeeded :: NoComp a b -> NoComp a' b' -> Maybe (NoComp (a,a') (b,b'), b')
succeeded nc (Pre i) = Just (nc :***: Id, i)
succeeded nc (a :***: b) = case isPre (a :***: b) of
    Just (Pre i) -> Just (nc :***: Id, i)
    _ -> Nothing
succeeded _ _ = Nothing

isPre :: NoComp a b -> Maybe (NoComp a b)
isPre (Pre i) = Just (Pre i)
isPre (a :***: b) = (:***:) <$> isPre a <*> isPre b
isPre _ = Nothing