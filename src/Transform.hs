{-# LANGUAGE ScopedTypeVariables, TypeOperators, StandaloneDeriving, DataKinds #-}

module Transform where

import ArrowCF
import Data.Maybe (fromJust)
import Control.Applicative
import Data.Type.Equality (type (:~~:)(..))
import Debug.Trace

data LoopBox a b where
    LB :: ValidDesc c => CF (P a c) (P b c) -> LoopBox a b
deriving instance Show (LoopBox a b)

-- Traverse the program to find Loop.
-- ASSUMPTION: We assume that we do not start with any LoopD or LoopM, or at least
-- that no LoopD/LoopM contain Loop.
transform :: CF a b -> CF a b
-- If we have a loop, go inside it, then once you're done transform that.
transform (Single (Loop f)) = transformLoop (LB $ transform f)
transform (Single (f :***: g)) = transform (Single f) *** transform (Single g)
transform (Single g) = Single g
-- If we have a composition, transform the elements of the composition.
transform (f :>>>: g) = transform f >>> transform g

-- The main transformation algorithm. Tries to transform to LoopM, and then LoopD.
transformLoop :: (ValidDesc a, ValidDesc b) => LoopBox a b -> CF a b
transformLoop lb = case (transformNoLoop lb <|> transformLoopM lb) <|> transformLoopD lb of
    Just cf -> cf
    Nothing -> error (show lb)

-- Attempt to apply loop (f *** g) = f, thus avoiding the problem altogether.
-- Since we have >>> at the top level, we need to check each part for ***.
transformNoLoop :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (CF a b)
transformNoLoop (LB cf) = case tailsForm cf of
    OnlyTails f g HRefl HRefl -> Just f
    _ -> Nothing

transformLoopM :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (CF a b)
transformLoopM (LB cf) = split cf >>=
    \(SR fl d fr) -> Just . Single . Dec $ LoopM fl d fr

transformLoopD :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (CF a b)
transformLoopD lb =
    -- TO VERIFY: I think we can just keep left sliding because
    -- the only case where that'll go infinite is the NoLoop case.
    case repeatMaybe leftSlide lb of
        LB cf -> case tailsForm cf of
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
        CF a b -> CF c d -> CF e f -> (b :~~: P c e) -> (g :~~: P d f) -> TailsForm a g
    OnlyTails :: (ValidDesc a, ValidDesc c, ValidDesc d, ValidDesc e, ValidDesc f, ValidDesc g) =>
        CF c d -> CF e f -> (a :~~: P c e) -> (g :~~: P d f) -> TailsForm a g
    NoTails :: (ValidDesc a, ValidDesc g) => CF a g -> TailsForm a g
deriving instance Show (TailsForm a g)

tailsForm :: forall a b. (ValidDesc a, ValidDesc b) =>
    CF a b -> TailsForm a b
tailsForm cf =
    case initLast cf of
        Left singl -> case unPar singl of
            Just (UP f g HRefl HRefl) -> OnlyTails (Single f) (Single g) HRefl HRefl
            Nothing -> NoTails cf
        Right (IL i l) -> case unPar l of
            Just (UP f g HRefl HRefl) -> tailsForm' i (Single f) (Single g)
            Nothing -> NoTails cf
    where
        tailsForm' :: (ValidDesc c, ValidDesc d, ValidDesc e, ValidDesc f) =>
            CF a (P c d) -> CF c e -> CF d f -> TailsForm a (P e f)
        tailsForm' cf' tl tr =
            case initLast cf' of
                Left singl -> case unPar singl of
                    Nothing -> TF cf' tl tr HRefl HRefl
                    Just (UP f g HRefl HRefl) -> OnlyTails (Single f >>> tl) (Single g >>> tr) HRefl HRefl
                Right (IL i l) -> case unPar l of
                    Nothing -> TF cf' tl tr HRefl HRefl
                    Just (UP f g HRefl HRefl) -> tailsForm' i (Single f >>> tl) (Single g >>> tr)

-- Have to do this to allow for reasonable return types.
data Tightening a f where
    TG :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d, ValidDesc e, ValidDesc f) =>
        CF a b -> CF (P b d) (P c e) -> CF c f -> Decoupled e d -> Tightening a f
deriving instance Show (Tightening a f)

-- Apply left/right tightening to the CF.
-- Use left/right fill to aid the process.
tightening :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d)
    => CF (P a c) (P b d) -> Decoupled d c -> CF a b
tightening cf dec = tighteningToCF $ leftTighten $ rightTighten (TG id_ cf id_ dec)
    where
        tighteningToCF :: Tightening a b -> CF a b
        tighteningToCF (TG l cf r dec) =
            l >>> Single (LoopD cf dec) >>> r
        rightTighten :: Tightening a b -> Tightening a b
        rightTighten (TG l cf r dec) = case initLast (push cf) of
            Right (IL ss (f :***: g)) ->
                -- Check we're not trying to slide id, because that will go infinite.
                -- rightTighten (TG l (ss >>> (f :***: g)) r dec)
                -- => rightTighten (TG l (ss >>> (id :***: g)) (f >>> r) dec)
                -- which are identical if f = Id
                -- We therefore stop recursion if f = Id.
                case isId f of
                    Just HRefl -> TG l cf r dec
                    Nothing -> rightTighten (TG l (ss >>> Single (idNoComp :***: g)) (Single f >>> r) dec)
            _ -> TG l cf r dec
        leftTighten :: Tightening a b -> Tightening a b
        leftTighten (TG l cf r dec) = case headTail (pushBack cf) of
            Right (HT (f :***: g) ss) ->
                -- Check we're not trying to slide id, because that will go infinite (see rightTighten).
                case isId f of
                    Just HRefl -> TG l cf r dec
                    Nothing -> leftTighten (TG (l >>> Single f) (Single (idNoComp :***: g) >>> ss) r dec)
            _ -> TG l cf r dec

-- Move all non-ID terms to the left.
pushBack :: CF a b -> CF a b
pushBack cf = case initLast cf of
    Left _ -> cf
    Right (IL an f) -> case initLast an of
        Left an' -> compTwoCompose $ fillBack (C2 an' f)
        Right (IL a n) ->
            pushBack' a $ fillBack (C2 n f)
    where
        pushBack' :: ValidDesc a => CF a b -> CompTwo b c -> CF a c
        pushBack' a (C2 n' f') = pushBack (a >>> Single n') >>> Single f'
        fillBack :: CompTwo a b -> CompTwo a b
        fillBack (C2 (f :***: g) (h :***: i)) =
            compTwoPar (fillBack $ C2 f h) (fillBack $ C2 g i)
        fillBack (C2 f g) = case isId f of
            Just HRefl -> C2 g idNoComp 
            Nothing -> C2 f g

-- Move all non-ID terms to the right.
push :: CF a b -> CF a b
push cf = case headTail cf of
    Left _ -> cf
    Right (HT a nf) -> case headTail nf of
        Left nf' -> compTwoCompose $ fill (C2 a nf')
        Right (HT n f) ->
            push' (fill (C2 a n)) f
    where
        push' :: ValidDesc c => CompTwo a b -> CF b c -> CF a c
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
        CF a b -> Decoupled b c -> CF c d -> SplitResult a d
deriving instance Show (SplitResult a d)

split :: (ValidDesc a, ValidDesc b) => CF a b -> Maybe (SplitResult a b)
split cf = case tailsForm cf of
        TF cf' f g HRefl HRefl ->
            case (,) <$> split f <*> split g of
                Just (SR fl fd fr, SR gl gd gr) ->
                    Just $ SR (cf' >>> (fl *** gl)) (BothDec fd gd) (fr *** gr)
                Nothing -> split cf' >>= \(SR al ad ar) -> Just $ SR al ad (ar >>> (f *** g))
        OnlyTails f g HRefl HRefl ->
            (,) <$> split f <*> split g >>= \(SR fl fd fr, SR gl gd gr) ->
                Just $ SR (fl *** gl) (BothDec fd gd) (fr *** gr)
        NoTails cf' -> case initLast cf' of
            Left singl -> asDecoupled singl >>= \dec -> Just $ SR id_ dec id_
            Right (IL i l) -> case asDecoupled l of
                Just dec -> Just $ SR i dec id_
                Nothing -> split i >>= \(SR il idec ir) -> Just $ SR il idec (ir >>> Single l)

leftSlide :: ValidDesc b => LoopBox a b -> Maybe (LoopBox a b)
leftSlide (LB cf) =
    case headTail (pushBack cf) of
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
rightSlide (LB cf) =
    case initLast (push cf) of
        Left _ -> Nothing
        Right (IL ss s) -> case s of
            s1 :***: s2 -> case isId s2 of
                Just HRefl -> Nothing
                Nothing -> Just $ LB $ (id_ *** Single s2) >>> ss >>> (Single s1 *** id_)
            _ -> Nothing