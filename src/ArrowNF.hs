module ArrowNF (module NF, module ArrowNF) where

import NF

import Prelude hiding (id)

data HeadTail a c where
    HT :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
        NoComp a b -> ANF b c -> HeadTail a c
data InitLast a c where
    IL :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
        ANF a b -> NoComp b c -> InitLast a c

headTail :: ANF a b -> Either (NoComp a b) (HeadTail a b)
headTail (Single a) = Left a
headTail (Single a :>>>: b) = Right $ HT a b
headTail (a :>>>: b) = case headTail a of
        Right ht -> Right $ htCompose ht b
        Left a' -> Right $ HT a' b
    where
        htCompose :: ValidDesc b =>
            HeadTail a x -> ANF x b -> HeadTail a b
        htCompose (HT ah at) b = HT ah (at :>>>: b)

initLast :: ANF a b -> Either (NoComp a b) (InitLast a b)
initLast (Single a) = Left a
initLast (a :>>>: Single b) = Right $ IL a b
initLast (a :>>>: b) = case initLast b of
        Right ht -> Right $ ilCompose a ht
        Left b' -> Right $ IL a b'
    where
        ilCompose :: ValidDesc a => ANF a x -> InitLast x b -> InitLast a b
        ilCompose a (IL bi bl) = IL (a :>>>: bi) bl

-- THE ARROW API FOR ANF

id :: ValidDesc a => ANF a a
id = id_

(>>>) :: (ValidDesc a, ValidDesc b, ValidDesc c) => ANF a b -> ANF b c -> ANF a c
f >>> g = f :>>>: g

arr :: (ValidDesc a, ValidDesc b) => (Val a -> Val b) -> ANF a b
arr = arr_

-- Need to apply distributive law here.
(***) :: (ValidDesc a, ValidDesc a', ValidDesc b, ValidDesc b') => ANF a b -> ANF a' b' -> ANF (P a a') (P b b')
(Single f) *** (Single g) = Single (f :***: g)
(f :>>>: f') *** (Single g) = (f *** Single g) :>>>: (f' *** id)
(Single f) *** (g :>>>: g') = (Single f *** g) :>>>: (id *** g')
(f :>>>: f') *** (g :>>>: g') = (f *** g) :>>>: (f' *** g')

first :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
    ANF a b -> ANF (P a c) (P b c)
first = (*** id)
second :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
    ANF a b -> ANF (P c a) (P c b)
second = (id ***)

loop :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
    ANF (P a c) (P b c) -> ANF a b
loop = undefined

pre :: ValidDesc a => Val a -> ANF a a
pre = pre_