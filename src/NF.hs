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

type ANF :: forall s s'. Desc s -> Desc s' -> *
data ANF x y where
    Loop :: ValidDesc c => NoLoop (P a c) (P b c) -> ANF a b
    WithoutLoop :: NoLoop a b -> ANF a b

infixl 1 :>>>:
type NoLoop :: forall s s'. Desc s -> Desc s' -> *
data NoLoop x y where
    (:>>>:) :: (ValidDesc b, ValidDesc c) => NoLoop a b -> NoComp b c -> NoLoop a c
    WithoutComp :: NoComp a b -> NoLoop a b

-- @CompTwo@ represents exactly two composed terms.
-- This is used to avoid some awkward pattern matching.
data CompTwo a c where
    C2 :: (ValidDesc b, ValidDesc c) => NoComp a b -> NoComp b c -> CompTwo a c

infixl 3 :***:
type NoComp :: forall s s'. Desc s -> Desc s' -> *
data NoComp x y where
    (:***:) :: (ValidDesc a, ValidDesc a', ValidDesc b, ValidDesc b') => NoComp a b -> NoComp a' b' -> NoComp (P a a') (P b b')
    Arr :: ValidDesc b => (Val a -> Val b) -> NoComp a b
    -- This forces Pre (Pair i j) to be represented as Pre i *** Pre j.
    Pre :: Val (V (a :: *)) -> NoComp (V a) (V a)
    -- NOTE: I've tried to split up Id like with Pre and it doesn't work. Type
    -- erasure means that defining something that takes in no arguments means
    -- it needs a context in order to determine how to proceed. And adding that
    -- context means including it everywhere, which is hellish.
    Id :: ValidDesc a => NoComp a a
    Assoc :: (ValidDesc a, ValidDesc b) => NoComp (P (P a b) c) (P a (P b c))
    Cossa :: (ValidDesc a, ValidDesc b, ValidDesc c) => NoComp (P a (P b c)) (P (P a b) c)
    Juggle :: (ValidDesc a, ValidDesc b) => NoComp (P (P a b) c) (P (P a c) b)
    Distribute :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d) => NoComp (P (P a b) (P c d)) (P (P a c) (P b d))
    Squish :: (ValidDesc a, ValidDesc b, ValidDesc c) => NoComp (P a (P b c)) (P b (P a c))

data ALP a b where
    LoopPre :: ValidDesc c => Val c -> NoLoop (P a c) (P b c) -> ALP a b
    WithoutLoopPre :: NoLoop a b -> ALP a b

-- * Show instances

instance Show a => Show (Val (V a)) where
    show (One a) = show a
instance (Show (Val a), Show (Val b)) => Show (Val (P a b)) where
    show (Pair a b) = "[|" ++ show a ++ ", " ++ show b ++ "|]"

instance Show (ANF a b) where
    show (Loop f) = "Loop " ++ show f
    show (WithoutLoop f) = show f

instance Show (NoLoop a b) where
    show (f :>>>: g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (WithoutComp f) = show f

instance Show (NoComp a b) where
    show (f :***: g) = "(" ++ show f ++ " *** " ++ show g ++ ")"
    show (Arr f) = "Arr"
    show (Pre a) = "Pre"
    show Id = "Id"
    show Assoc = "Assoc"
    show Cossa = "Cossa"
    show Juggle = "Juggle"
    show Distribute = "Distribute"
    show Squish = "Squish"

instance Show (ALP a b) where
    show (WithoutLoopPre f) = show f
    show (LoopPre c f) = "LoopPre " ++ show f

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

lift_ :: NoComp a b -> NoLoop a b
lift_ = WithoutComp

arr_ :: ValidDesc b => (Val a -> Val b) -> NoLoop a b
arr_ = WithoutComp . Arr

id_ :: ValidDesc a => NoLoop a a
id_ = WithoutComp Id

pre_ :: ValidDesc a => Val a -> NoLoop a a
pre_ = WithoutComp . preHelp
    where
        preHelp :: ValidDesc a => Val a -> NoComp a a
        preHelp (One a) = Pre (One a)
        preHelp (Pair a b) = preHelp a :***: preHelp b
