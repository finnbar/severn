module NFReversed where

import NF

-- TODO: Tests for reversing, because I'm not confident that invariants hold.
data Reversed x y where
    (:<<<:) :: NoComp a b -> Reversed b c -> Reversed a c
    WithoutCompRev :: NoComp a b -> Reversed a b

reverseNoLoop :: NoLoop a b -> Reversed a b
reverseNoLoop (WithoutComp f) = WithoutCompRev f
reverseNoLoop (WithoutComp f :>>>: g) = f :<<<: WithoutCompRev g
reverseNoLoop ((f :>>>: g) :>>>: h) = reverseHelper f (g :<<<: WithoutCompRev h)
    where
        reverseHelper :: NoLoop a b -> Reversed b c -> Reversed a c
        reverseHelper (WithoutComp f) rev = f :<<<: rev
        reverseHelper (f :>>>: g) rev =
            reverseHelper f (g :<<<: rev)

reverseReversed :: Reversed a b -> NoLoop a b
reverseReversed (WithoutCompRev f) = WithoutComp f
reverseReversed (f :<<<: WithoutCompRev g) = WithoutComp f :>>>: g
reverseReversed (f :<<<: (g :<<<: h)) = reverseHelper (WithoutComp f :>>>: g) h
    where
        reverseHelper :: NoLoop a b -> Reversed b c -> NoLoop a c
        reverseHelper rev (WithoutCompRev h) = rev :>>>: h
        reverseHelper rev (f :<<<: g) =
            reverseHelper (rev :>>>: f) g

compTwoComposeRev :: CompTwo a c -> Reversed a c
compTwoComposeRev (C2 Id y) = WithoutCompRev y
compTwoComposeRev (C2 x Id) = WithoutCompRev x
compTwoComposeRev (C2 x y) = x :<<<: WithoutCompRev y
