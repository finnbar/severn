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
    Pair :: (ValidDesc a, ValidDesc b) => Val a -> Val b -> Val (P a b)

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
-- Note that this may be at any stage of compilation, so could be a mix of
-- Loop/LoopD/LoopM.
infixl 1 :>>>:
type ANF :: forall s s'. Desc s -> Desc s' -> *
data ANF x y where
    (:>>>:) :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
        ANF a b -> ANF b c -> ANF a c
    Single :: (ValidDesc a, ValidDesc b) =>
        NoComp a b -> ANF a b

-- @CompTwo@ represents exactly two composed terms.
-- This is used to avoid some awkward pattern matching.
data CompTwo a c where
    C2 :: NoComp a b -> NoComp b c -> CompTwo a c

infixl 3 :***:
type NoComp :: forall s s'. Desc s -> Desc s' -> *
data NoComp x y where
    Loop :: (ValidDesc a, ValidDesc b, ValidDesc c) =>
        ANF (P a c) (P b c) -> NoComp a b
    LoopD :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d) =>
        ANF (P a c) (P b d) -> Decoupled d c -> NoComp a b
    (:***:) :: (ValidDesc a, ValidDesc a', ValidDesc b, ValidDesc b') =>
        NoComp a b -> NoComp a' b' -> NoComp (P a a') (P b b')
    Arr :: (ValidDesc a, ValidDesc b) =>
        (Val a -> Val b) -> NoComp a b
    -- This forces Id on tuple types to be reduced to Id *** Id.
    Id :: NoComp (V (a :: *)) (V a)
    Dec :: Decoupled a b -> NoComp a b

type Decoupled :: forall s s'. Desc s -> Desc s' -> *
data Decoupled a b where
    BothDec :: (ValidDesc a, ValidDesc b, ValidDesc a', ValidDesc b') =>
        Decoupled a b -> Decoupled a' b' -> Decoupled (P a a') (P b b')
    LoopM :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d, ValidDesc e) =>
        ANF (P a c) d -> Decoupled d e -> ANF e (P b c) -> Decoupled a b
    -- This forces Pre (Pair i j) to be represented as Pre i *** Pre j.
    Pre :: ValidDesc (V a) =>
        Val (V (a :: *)) -> Decoupled (V a) (V a)

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
    show (LoopD f dec) = "LoopD (" ++ show f ++ ") (" ++ show dec ++ ")"
    show (f :***: g) = "(" ++ show f ++ " *** " ++ show g ++ ")"
    show (Arr f) = "Arr"
    show Id = "Id"
    show (Dec d) = show d

instance Show (Decoupled a b) where
    show (BothDec f g) = "(" ++ show f ++ " *** " ++ show g ++ ")"
    show (LoopM f d g) = "LoopM (" ++ show f ++ ") (" ++ show d ++ ") (" ++ show g ++ ")"
    show (Pre v) = "Pre"

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

lift_ :: (ValidDesc a, ValidDesc b) => NoComp a b -> ANF a b
lift_ = Single

arr_ :: (ValidDesc a, ValidDesc b) => (Val a -> Val b) -> ANF a b
arr_ = Single . Arr

id_ :: ValidDesc a => ANF a a
id_ = Single (generateId (Proxy :: Proxy a))

pre_ :: ValidDesc a => Val a -> ANF a a
pre_ = Single . preHelp
    where
        preHelp :: ValidDesc a => Val a -> NoComp a a
        preHelp (One a) = Dec $ Pre (One a)
        preHelp (Pair a b) = preHelp a :***: preHelp b
