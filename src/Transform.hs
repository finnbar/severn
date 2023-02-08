{-# LANGUAGE ScopedTypeVariables, TypeOperators, StandaloneDeriving #-}

module Transform where

import ArrowNF
import Data.Maybe (fromJust)
import Control.Applicative
import Data.Type.Equality (type (:~~:)(..))
import Debug.Trace

data LoopBox a b where
    LB :: ValidDesc c => ANF (P a c) (P b c) -> LoopBox a b
deriving instance Show (LoopBox a b)

-- Traverse the program to find Loop.
-- ASSUMPTION: We assume that we do not start with any LoopD or LoopM, or at least
-- that no LoopD/LoopM contain Loop.
transform :: ANF a b -> ANF a b
-- If we have a loop, go inside it, then once you're done transform that.
transform (Single (Loop f)) = transformLoop (LB $ transform f)
transform (Single (f :***: g)) = transform (Single f) *** transform (Single g)
transform (Single g) = Single g
-- If we have a composition, transform the elements of the composition.
transform (f :>>>: g) = transform f >>> transform g

-- The main transformation algorithm. Tries to transform to LoopM, and then LoopD.
transformLoop :: (ValidDesc a, ValidDesc b) => LoopBox a b -> ANF a b
transformLoop lb = case (transformNoLoop lb <|> transformLoopM lb) <|> transformLoopD lb of
    Just anf -> anf
    Nothing -> error (show lb)

-- Attempt to apply loop (f *** g) = f, thus avoiding the problem altogether.
-- Since we have >>> at the top level, we need to check each part for ***.
transformNoLoop :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (ANF a b)
transformNoLoop (LB anf) = case tailsForm anf of
    OnlyTails f g HRefl HRefl -> Just f
    _ -> Nothing

transformLoopM :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (ANF a b)
transformLoopM (LB anf) = split anf >>=
    \(SR fl d fr) -> Just . Single . Dec $ LoopM fl d fr

transformLoopD :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (ANF a b)
transformLoopD lb =
    -- TO VERIFY: I think we can just keep left sliding because
    -- the only case where that'll go infinite is the NoLoop case.
    case repeatMaybe leftSlide lb of
        LB anf -> case tailsForm anf of
            -- loop (f >>> (g *** h))
            TF f g h HRefl HRefl -> split h >>= \(SR hl d hr) ->
                Just $ tightening (second hr >>> f >>> (g *** hl)) d
            -- OnlyTails should have been caught earlier by transformNoLoop.
            _ -> Nothing
    where
        repeatMaybe :: (a -> Maybe a) -> a -> a
        repeatMaybe f x = case f x of
            Just x' -> repeatMaybe f x'
            Nothing -> x

data TailsForm a g where
    TF :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d, ValidDesc e, ValidDesc f, ValidDesc g) =>
        ANF a b -> ANF c d -> ANF e f -> (b :~~: P c e) -> (g :~~: P d f) -> TailsForm a g
    OnlyTails :: (ValidDesc a, ValidDesc c, ValidDesc d, ValidDesc e, ValidDesc f, ValidDesc g) =>
        ANF c d -> ANF e f -> (a :~~: P c e) -> (g :~~: P d f) -> TailsForm a g
    NoTails :: (ValidDesc a, ValidDesc g) => ANF a g -> TailsForm a g
deriving instance Show (TailsForm a g)

tailsForm :: forall a b. (ValidDesc a, ValidDesc b) =>
    ANF a b -> TailsForm a b
tailsForm anf =
    case initLast anf of
        Left singl -> case unPar singl of
            Just (UP f g HRefl HRefl) -> OnlyTails (Single f) (Single g) HRefl HRefl
            Nothing -> NoTails anf
        Right (IL i l) -> case unPar l of
            Just (UP f g HRefl HRefl) -> tailsForm' i (Single f) (Single g)
            Nothing -> NoTails anf
    where
        tailsForm' :: (ValidDesc c, ValidDesc d, ValidDesc e, ValidDesc f) =>
            ANF a (P c d) -> ANF c e -> ANF d f -> TailsForm a (P e f)
        tailsForm' anf' tl tr =
            case initLast anf' of
                Left singl -> case unPar singl of
                    Nothing -> TF anf' tl tr HRefl HRefl
                    Just (UP f g HRefl HRefl) -> OnlyTails (Single f >>> tl) (Single g >>> tr) HRefl HRefl
                Right (IL i l) -> case unPar l of
                    Nothing -> TF anf' tl tr HRefl HRefl
                    Just (UP f g HRefl HRefl) -> tailsForm' i (Single f >>> tl) (Single g >>> tr)

-- Have to do this to allow for reasonable return types.
data Tightening a f where
    TG :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d, ValidDesc e, ValidDesc f) =>
        ANF a b -> ANF (P b d) (P c e) -> ANF c f -> Decoupled e d -> Tightening a f
deriving instance Show (Tightening a f)

-- Apply left/right tightening to the ANF.
-- Use left/right fill to aid the process.
tightening :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d)
    => ANF (P a c) (P b d) -> Decoupled d c -> ANF a b
tightening anf dec = tighteningToANF $ leftTighten $ rightTighten (TG id_ anf id_ dec)
    where
        tighteningToANF :: Tightening a b -> ANF a b
        tighteningToANF (TG l anf r dec) =
            l >>> Single (LoopD anf dec) >>> r
        rightTighten :: Tightening a b -> Tightening a b
        rightTighten (TG l anf r dec) = case initLast (push anf) of
            Right (IL ss (f :***: g)) ->
                -- Check we're not trying to slide id, because that will go infinite.
                -- rightTighten (TG l (ss >>> (f :***: g)) r dec)
                -- => rightTighten (TG l (ss >>> (id :***: g)) (f >>> r) dec)
                -- which are identical if f = Id
                -- We therefore stop recursion if f = Id.
                case isId f of
                    Just HRefl -> TG l anf r dec
                    Nothing -> rightTighten (TG l (ss >>> Single (idNoComp :***: g)) (Single f >>> r) dec)
            _ -> TG l anf r dec
        leftTighten :: Tightening a b -> Tightening a b
        leftTighten (TG l anf r dec) = case headTail (pushBack anf) of
            Right (HT (f :***: g) ss) ->
                -- Check we're not trying to slide id, because that will go infinite (see rightTighten).
                case isId f of
                    Just HRefl -> TG l anf r dec
                    Nothing -> leftTighten (TG (l >>> Single f) (Single (idNoComp :***: g) >>> ss) r dec)
            _ -> TG l anf r dec

-- Move all non-ID terms to the left.
pushBack :: ANF a b -> ANF a b
pushBack anf = case initLast anf of
    Left _ -> anf
    Right (IL an f) -> case initLast an of
        Left an' -> compTwoCompose $ fillBack (C2 an' f)
        Right (IL a n) ->
            pushBack' a $ fillBack (C2 n f)
    where
        pushBack' :: ValidDesc a => ANF a b -> CompTwo b c -> ANF a c
        pushBack' a (C2 n' f') = pushBack (a >>> Single n') >>> Single f'
        fillBack :: CompTwo a b -> CompTwo a b
        fillBack (C2 (f :***: g) (h :***: i)) =
            compTwoPar (fillBack $ C2 f h) (fillBack $ C2 g i)
        fillBack (C2 f g) = case isId f of
            Just HRefl -> C2 g idNoComp 
            Nothing -> C2 f g

-- Move all non-ID terms to the right.
push :: ANF a b -> ANF a b
push anf = case headTail anf of
    Left _ -> anf
    Right (HT a nf) -> case headTail nf of
        Left nf' -> compTwoCompose $ fill (C2 a nf')
        Right (HT n f) ->
            push' (fill (C2 a n)) f
    where
        push' :: ValidDesc c => CompTwo a b -> ANF b c -> ANF a c
        push' (C2 a' n') f = Single a' >>> push (Single n' >>> f)
        fill :: CompTwo a b -> CompTwo a b
        fill (C2 (f :***: g) (h :***: i)) =
            compTwoPar (fill $ C2 f h) (fill $ C2 g i)
        fill (C2 f g) = case isId g of
            Just HRefl -> C2 idNoComp f
            Nothing -> C2 f g

asDecoupled :: NoComp a b -> Maybe (Decoupled a b)
asDecoupled (Dec d) = Just d
asDecoupled (f :***: g) = do
    fd <- asDecoupled f
    gd <- asDecoupled g
    return $ BothDec fd gd
asDecoupled _ = Nothing

data SplitResult a d where
    SR :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d) =>
        ANF a b -> Decoupled b c -> ANF c d -> SplitResult a d
deriving instance Show (SplitResult a d)

split :: (ValidDesc a, ValidDesc b) => ANF a b -> Maybe (SplitResult a b)
split anf = case tailsForm anf of
        TF anf' f g HRefl HRefl ->
            case (,) <$> split f <*> split g of
                Just (SR fl fd fr, SR gl gd gr) ->
                    Just $ SR (anf' >>> (fl *** gl)) (BothDec fd gd) (fr *** gr)
                Nothing -> split anf' >>= \(SR al ad ar) -> Just $ SR al ad (ar >>> (f *** g))
        OnlyTails f g HRefl HRefl ->
            (,) <$> split f <*> split g >>= \(SR fl fd fr, SR gl gd gr) ->
                Just $ SR (fl *** gl) (BothDec fd gd) (fr *** gr)
        NoTails anf' -> case initLast anf' of
            Left singl -> asDecoupled singl >>= \dec -> Just $ SR id_ dec id_
            Right (IL i l) -> case asDecoupled l of
                Just dec -> Just $ SR i dec id_
                Nothing -> split i >>= \(SR il idec ir) -> Just $ SR il idec (ir >>> Single l)

leftSlide :: ValidDesc b => LoopBox a b -> Maybe (LoopBox a b)
leftSlide (LB anf) =
    case headTail anf of
        Left _ -> Nothing
        Right (HT s ss) -> case s of
            s1 :***: s2 -> case isId s2 of
                -- If it's Id, you cannot slide further -- the removeId should mean that
                -- there being Id here => can't slide something useful in that slot.
                Just HRefl -> Nothing
                Nothing -> Just $ LB $ (Single s1 *** id_) >>> ss >>> (id_ *** Single s2)
            -- impossible to slide
            _ -> Nothing

rightSlide :: ValidDesc a => LoopBox a b -> Maybe (LoopBox a b)
rightSlide (LB anf) =
    case initLast anf of
        Left _ -> Nothing
        Right (IL ss s) -> case s of
            s1 :***: s2 -> case isId s2 of
                Just HRefl -> Nothing
                Nothing -> Just $ LB $ (id_ *** Single s2) >>> ss >>> (Single s1 *** id_)
            _ -> Nothing