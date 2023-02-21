{-# LANGUAGE TypeOperators, DataKinds #-}

module ArrowCF (module ComposedForm, module ArrowCF) where

-- The Arrow API for CFs, along with a few helper functions.

import ComposedForm

import Prelude hiding (id)
import Data.Type.Equality (type (:~~:)(..))

data HeadTail a c where
    HT :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
        NoComp a b -> CF b c -> HeadTail a c
data InitLast a c where
    IL :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
        CF a b -> NoComp b c -> InitLast a c

headTail :: CF a b -> Either (NoComp a b) (HeadTail a b)
headTail (Single a) = Left a
headTail (Single a :>>>: b) = case isId a of
    Just HRefl -> headTail b
    Nothing -> Right $ HT a b
headTail (a :>>>: b) = case headTail a of
        Right ht -> Right $ htCompose ht b
        Left a' -> Right $ HT a' b
    where
        htCompose :: ValidDesc b =>
            HeadTail a x -> CF x b -> HeadTail a b
        htCompose (HT ah at) b = HT ah (at :>>>: b)

initLast :: CF a b -> Either (NoComp a b) (InitLast a b)
initLast (Single a) = Left a
initLast (a :>>>: Single b) = case isId b of
    Just HRefl -> initLast a
    Nothing -> Right $ IL a b
initLast (a :>>>: b) = case initLast b of
        Right ht -> Right $ ilCompose a ht
        Left b' -> Right $ IL a b'
    where
        ilCompose :: ValidDesc a => CF a x -> InitLast x b -> InitLast a b
        ilCompose a (IL bi bl) = IL (a :>>>: bi) bl

-- THE ARROW API FOR CF

id :: ValidDesc a => CF a a
id = id_

(>>>) :: (ValidDesc a, ValidDesc b, ValidDesc c) => CF a b -> CF b c -> CF a c
f >>> g = removeId $ f :>>>: g

arr :: (ValidDesc a, ValidDesc b) => (Val a -> Val b) -> CF a b
arr = arr_

-- Need to apply distributive law here.
(***) :: (ValidDesc a, ValidDesc a', ValidDesc b, ValidDesc b') => CF a b -> CF a' b' -> CF (P a a') (P b b')
(Single f) *** (Single g) = Single (f :***: g)
(f :>>>: f') *** (Single g) = (f *** Single g) :>>>: (f' *** id)
(Single f) *** (g :>>>: g') = (Single f *** g) :>>>: (id *** g')
(f :>>>: f') *** (g :>>>: g') = (f *** g) :>>>: (f' *** g')

first :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
    CF a b -> CF (P a c) (P b c)
first = (*** id)
second :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
    CF a b -> CF (P c a) (P c b)
second = (id ***)

loop :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
    CF (P a c) (P b c) -> CF a b
loop = Single . Loop

pre :: ValidDesc a => Val a -> CF a a
pre = pre_