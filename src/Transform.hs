{-# LANGUAGE FlexibleInstances #-}

module Transform where

import ArrowNF

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

transform :: ANF a b -> ALP a b
transform (WithoutLoop f) = WithoutLoopPre f
transform (Loop (WithoutComp f)) = case f of
    -- Reached a success condition. (1)
    nc :***: (Pre i) -> LoopPre i (WithoutComp (nc :***: Id))
    -- Product rule then success (pre (i,j) = pre i *** pre j). (2)
    Pre (i,j) -> LoopPre j (WithoutComp (Pre i :***: Id))
    -- No rules can be applied.
    _ -> error "Cannot convert into loopPre."
transform (Loop (a :>>>: f)) = case f of
    -- Reached a success condition. (1)
    nc :***: Pre i -> LoopPre i (a :>>>: (nc :***: Id))
    -- Use right sliding (loop (a >>> (b *** c)) = loop ((id *** c) >>> a >>> (b *** id)))
    -- NOTE: will need some kind of squishing rule maybe to deal with b *** id
    -- (e.g. if we have a *** b >>> c *** id, we can have a *** id >>> c *** b, and c *** b might fit Pre rule)
    nc :***: nc' -> transform $ Loop $ WithoutComp (Id :***: nc') `comp` a :>>>: nc :***: Id
    -- Product rule then success. (2)
    Pre (i,j) -> LoopPre j (a :>>>: (Pre i :***: Id))
    x -> _ -- TODO: squash / reverse squash

{-
rotateUntilPre :: NoLoop (a,c) (b,c) -> (c, NoLoop (a,c) (b,c))
-- Success condition
rotateUntilPre (a :>>>: (b :***: (Pre i)))
    = (i, a :>>>: (b :***: WithoutPar (Arr id)))
-- Use product rule pre i *** pre j = pre (i,j)
rotateUntilPre (a :>>>: Pre (i,j))
    = (j, a :>>>: (WithoutPar (Pre i) :***: WithoutPar (Arr id)))
-- Use sliding to move Arr
-- TODO: This errors because the type changes - may have to reconsider slightly.
-- Answer is likely to change this so it is still enclosed in Loop.
-- Also maybe some helpers would make this less awful.
rotateUntilPre (a :>>>: (b :***: Arr f))
    = rotateUntilPre (WithoutComp (WithoutPar (Arr id) :***: WithoutPar (Arr f)) `comp` a :>>>: (b :***: WithoutPar (Arr id)))
-}