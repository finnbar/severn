{-# LANGUAGE StandaloneKindSignatures, DataKinds, PolyKinds, RankNTypes,
    FlexibleContexts, TypeOperators #-}

module NF where

import Data.Proxy

-- * Data types and constructors

-- Trick taken from Guerric Chupin's SFRP implementation.
-- This avoids weird tuple types.
infixr 3 <>
data (<>) a b

type Desc :: * -> *
data Desc x where
    V :: a -> Desc a
    P :: Desc a -> Desc b -> Desc (a <> b)

type Val :: forall s. Desc s -> *
data Val x where
    One :: a -> Val (V a)
    Pair :: Val a -> Val b -> Val (P a b)

class ValidDesc a where
    emptyVal :: Proxy a -> Val a
    generateId :: Proxy a -> NoComp a a

instance ValidDesc (V a :: Desc *) where
    emptyVal _ = One undefined
    generateId _ = Id

instance (ValidDesc a, ValidDesc b) => ValidDesc (P a b) where
    emptyVal Proxy = Pair (emptyVal (Proxy :: Proxy a)) $ emptyVal (Proxy :: Proxy b)
    generateId Proxy = generateId (Proxy :: Proxy a) :***: generateId (Proxy :: Proxy b)

-- ArrowNormalForm, so we force >>> to be at the top level of each loop.
infixl 1 :>>>:
type ANF :: forall s s'. Desc s -> Desc s' -> *
data ANF x y where
    (:>>>:) :: ANF a b -> ANF b c -> ANF a c
    Single :: NoComp a b -> ANF a b

-- @CompTwo@ represents exactly two composed terms.
-- This is used to avoid some awkward pattern matching.
data CompTwo a c where
    C2 :: NoComp a b -> NoComp b c -> CompTwo a c

data HeadTail a c where
    HT :: NoComp a b -> ANF b c -> HeadTail a c
data InitLast a c where
    IL :: ANF a b -> NoComp b c -> InitLast a c

headTail :: ANF a b -> HeadTail a b
headTail (Single a) = HT a (Single Id)
headTail (Single a :>>>: b) = HT a b
headTail (a :>>>: b) = htCompose (headTail a) b
    where
        htCompose :: HeadTail a x -> ANF x b -> HeadTail a b
        htCompose (HT ah at) b = HT ah (at :>>>: b)

initLast :: ANF a b -> InitLast a b
initLast (Single a) = IL (Single Id) a
initLast (a :>>>: Single b) = IL a b
initLast (a :>>>: b) = ilCompose a (initLast b)
    where
        ilCompose :: ANF a x -> InitLast x b -> InitLast a b
        ilCompose a (IL bi bl) = IL (a :>>>: bi) bl

infixl 3 :***:
type NoComp :: forall s s'. Desc s -> Desc s' -> *
data NoComp x y where
    Loop :: ANF (P a c) (P b c) -> NoComp a b
    (:***:) :: NoComp a b -> NoComp a' b' -> NoComp (P a a') (P b b')
    Arr :: (Val a -> Val b) -> NoComp a b
    -- This forces Pre (Pair i j) to be represented as Pre i *** Pre j.
    Pre :: Val (V (a :: *)) -> NoComp (V a) (V a)
    -- NOTE: I've tried to split up Id like with Pre and it doesn't work. Type
    -- erasure means that defining something that takes in no arguments means
    -- it needs a context in order to determine how to proceed. And adding that
    -- context means including it everywhere, which is hellish.
    Id :: NoComp a a

-- ArrowLoopPre, which replaces Loop with LoopD and LoopM, and introduces
-- decoupled signal functions.
type ALP :: forall s s'. Desc s -> Desc s' -> *
data ALP a b where
    (:>>>>:) :: ALP a b -> ALP b c -> ALP a c
    Sing :: NoComp' a b -> ALP a b

type NoComp' :: forall s s'. Desc s -> Desc s' -> *
data NoComp' a b where
    LoopD :: ALP (P a c) (P b d) -> Decoupled d c -> NoComp' a b
    (:****:) :: NoComp' a b -> NoComp' a' b' -> NoComp' (P a a') (P b b')
    Arr' :: (Val a -> Val b) -> NoComp' a b
    Id' :: NoComp' a a
    Dec :: Decoupled a b -> NoComp' a b

type Decoupled :: forall s s'. Desc s -> Desc s' -> *
data Decoupled a b where
    BothDec :: Decoupled a b -> Decoupled a' b' -> Decoupled (P a a') (P b b')
    LoopM :: ALP (P a c) d -> Decoupled d e -> ALP e (P b c) -> Decoupled a b
    Pre' :: Val (V (a :: *)) -> Decoupled (V a) (V a)

-- * Show instances

instance Show a => Show (Val (V a)) where
    show (One a) = show a
instance (Show (Val a), Show (Val b)) => Show (Val (P a b)) where
    show (Pair a b) = "[|" ++ show a ++ ", " ++ show b ++ "|]"

instance Show (ANF a b) where
    show (f :>>>: g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (Single f) = show f

instance Show (NoComp a b) where
    show (Loop f) = "Loop (" ++ show f ++ ")"
    show (f :***: g) = "(" ++ show f ++ " *** " ++ show g ++ ")"
    show (Arr f) = "Arr"
    show (Pre a) = "Pre"
    show Id = "Id"

instance Show (ALP a b) where
    show (f :>>>>: g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (Sing f) = show f

instance Show (NoComp' a b) where
    show (LoopD f dec) = "LoopD (" ++ show f ++ ") (" ++ show dec ++ ")"
    show (f :****: g) = "(" ++ show f ++ " *** " ++ show g ++ ")"
    show (Arr' f) = "Arr"
    show Id' = "Id"
    show (Dec f) = show f

instance Show (Decoupled a b) where
    show (BothDec f g) = "(" ++ show f ++ " *** " ++ show g ++ ")"
    show (LoopM f d g) = "LoopM (" ++ show f ++ ") (" ++ show d ++ ") (" ++ show g ++ ")"
    show (Pre' v) = "Pre"

-- * Eq instances

-- This is an extremely dodgy Eq instance, but it does the job - our `show`
-- correctly notes precedence. We do not compare Arrs and Pres (cannot determine
-- function equality, nor guarantee variable equality due to hidden types
-- within our GADTs), but everything else compares correctly.
instance Eq (ANF a b) where
    f == f' = show f == show f'

instance Eq a => Eq (Val (V a)) where
    One a == One b = a == b

instance (Eq (Val a), Eq (Val b)) => Eq (Val (P a b)) where
    Pair a b == Pair a' b' = a == a' && b == b'

-- Helper lift functions

lift_ :: NoComp a b -> ANF a b
lift_ = Single

arr_ :: (Val a -> Val b) -> ANF a b
arr_ = Single . Arr

id_ :: ANF a a
id_ = Single Id

pre_ :: Val a -> ANF a a
pre_ = Single . preHelp
    where
        preHelp :: Val a -> NoComp a a
        preHelp (One a) = Pre (One a)
        preHelp (Pair a b) = preHelp a :***: preHelp b
