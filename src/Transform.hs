{-# LANGUAGE FlexibleInstances #-}

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
    -- Reached a success condition. (1)
    -- TODO: need a way of merging Pres if needed.
    nc :***: Pre i -> LoopPre i (a :>>>: (nc :***: Id))
    -- Use right sliding (loop (a >>> (b *** c)) = loop ((id *** c) >>> a >>> (b *** id))). (3)
    -- `throughComps squashRight` moves all useful information to the right.
    nc :***: nc' -> transform $ Loop $ throughComps squashRight (WithoutComp (Id :***: nc') `comp` a) $ WithoutComp (nc :***: Id)
    -- Product rule then success. (2)
    Pre (i,j) -> LoopPre j (a :>>>: (Pre i :***: Id))
    -- TODO: Reverse squash (5)
    -- Left squash. (4)
    _ -> transform $ Loop $ WithoutComp (Arr squish) `comp` (WithoutComp Id `par` prog)
