{-# LANGUAGE ScopedTypeVariables, TypeOperators #-}

module Transform where

import ArrowNF
import Data.Maybe (fromJust)
import Control.Applicative
import Data.Type.Equality (type (:~~:)(..))
import Data.Proxy
import Debug.Trace

data LoopBox a b where
    LB :: ValidDesc c => ANF (P a c) (P b c) -> LoopBox a b

instance Show (LoopBox a b) where
    show (LB anf) = show anf

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
transformLoop lb = fromJust $ (transformNoLoop lb <|> transformLoopM lb) <|> transformLoopD lb

-- Attempt to apply loop (f *** g) = f, thus avoiding the problem altogether.
-- Since we have >>> at the top level, we need to check each part for ***.
transformNoLoop :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (ANF a b)
transformNoLoop (LB anf) = getFirstComp anf
    where
        getFirstComp :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d)
            => ANF (P a b) (P c d) -> Maybe (ANF a c)
        getFirstComp anf = case headTail anf of
            Left singl -> unPar singl >>= \(UP l r HRefl HRefl) -> Just (Single l)
            Right (HT a b) -> unPar a >>=
                \(UP l r HRefl HRefl) -> (Single l >>>) <$> getFirstComp b

transformLoopM :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (ANF a b)
transformLoopM (LB anf) = split anf >>=
    \(SR fl d fr) -> Just . Single . Dec $ LoopM fl d fr

transformLoopD :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (ANF a b)
transformLoopD lb =
    -- TO VERIFY: I think we can just keep left sliding because
    -- the only case where that'll go infinite is the NoLoop case.
    let lb' = repeatMaybe leftSlide lb
    in case tailForm lb' of
        -- loop (f >>> second x)
        TF f x -> split x >>= \(SR xl d xr) ->
            Just . Single $ LoopD (second xr >>> f >>> second xl) d
    where
        repeatMaybe :: (a -> Maybe a) -> a -> a
        repeatMaybe f x = case f x of
            Just x' -> repeatMaybe f x'
            Nothing -> x

data TailForm a b where
    TF :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d) =>
        ANF (P a c) (P b d) -> ANF d c -> TailForm a b

tailForm :: forall a b. (ValidDesc a, ValidDesc b) =>
    LoopBox a b -> TailForm a b
tailForm (LB anf) = tailFormHelper anf id_ id_
    where
        tailFormHelper :: (ValidDesc c, ValidDesc x, ValidDesc y) =>
            ANF (P a c) (P x y) -> ANF x b -> ANF y c -> TailForm a b
        tailFormHelper anf' tailL tailR =
            case initLast anf' of
                Left singl -> case unPar singl of
                    Nothing -> TF (anf' >>> first tailL) tailR
                    Just (UP f g HRefl HRefl) ->
                        tailFormHelper id_ (Single f >>> tailL) (Single g >>> tailR)
                Right (IL i l) -> case unPar l of
                    Nothing -> TF (anf' >>> first tailL) tailR
                    Just (UP f g HRefl HRefl) ->
                        tailFormHelper i (Single f >>> tailL) (Single g >>> tailR)

-- Have to do this to allow for reasonable return types.
data Tightening a f where
    TG :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d, ValidDesc e, ValidDesc f) =>
        ANF a b -> ANF (P b d) (P c e) -> ANF c f -> Decoupled e d -> Tightening a f

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

-- Apply right extract to the input term, returning a composition
extract :: (ValidDesc a, ValidDesc b) => NoComp a b -> CompTwo a b
extract (Dec d) = C2 (Dec d) idNoComp
extract (f :***: g) = compTwoPar (extract f) (extract g)
extract f = C2 idNoComp f

data CompThree a d where
    C3 :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d) =>
        NoComp a b -> NoComp b c -> NoComp c d -> CompThree a d

instance Show (CompThree a d) where
    show (C3 a b c) = show a ++ " " ++ show b ++ " " ++ show c

displace :: (ValidDesc a, ValidDesc b) => CompTwo a b -> CompThree a b
displace (C2 (f :***: g) (h :***: i)) = compThreePar (displace (C2 f h)) (displace (C2 g i))
    where
        compThreePar :: CompThree x y -> CompThree x' y' -> CompThree (P x x') (P y y')
        compThreePar (C3 f1 f2 f3) (C3 g1 g2 g3) = C3 (f1 :***: g1) (f2 :***: g2) (f3 :***: g3)
displace (C2 f d) = case asDecoupled d of
    Nothing -> C3 (generateId (Proxy :: Proxy a)) f d
    Just d' -> C3 f (Dec d') (generateId (Proxy :: Proxy b))

fill :: CompTwo a b -> CompTwo a b
fill (C2 (f :***: g) (h :***: i)) =
    compTwoPar (fill $ C2 f h) (fill $ C2 g i)
fill (C2 f g) = case isId g of
    Just HRefl -> C2 idNoComp f
    Nothing -> C2 f g

fillBack :: CompTwo a b -> CompTwo a b
fillBack (C2 (f :***: g) (h :***: i)) =
    compTwoPar (fillBack $ C2 f h) (fillBack $ C2 g i)
fillBack (C2 f g) = case isId f of
    Just HRefl -> C2 g idNoComp 
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
    
instance Show (SplitResult a d) where
    show (SR a d b) = show a ++ " " ++ show d ++ " " ++ show b

split :: (ValidDesc a, ValidDesc b) => ANF a b -> Maybe (SplitResult a b)
split = flip splitHelper id_
    where
        splitHelper :: (ValidDesc x, ValidDesc y, ValidDesc z) =>
            ANF x y -> ANF y z -> Maybe (SplitResult x z)
        splitHelper anf ex = traceShow anf $ case initLast (push anf) of
            -- If we only have one element, it must be the pre or we fail.
            Left f -> asDecoupled f >>= \dec -> Just (SR id_ dec ex)
            -- pres = pre v is equivalent to l = pre v
            -- (since extract (pre v) = pre v >>> id so pres = pre v)
            Right (IL ini l) -> case asDecoupled l of
                Just dec -> Just (SR ini dec ex)
                -- Perform the extract
                Nothing ->
                    -- TODO this is a correct implementation of incorrect theory.
                    case initLast ini of
                        Right (IL i ni) ->
                            case displace (C2 ni l) of
                                C3 n' i' l' ->
                                    splitHelper (i >>> Single n' >>> Single i') (Single l' >>> ex)
                        Left sing ->
                            case displace (C2 sing l) of
                                C3 n' i' l' ->
                                    splitHelper (Single n' >>> Single i') (Single l' >>> ex)

leftSlide :: ValidDesc b => LoopBox a b -> Maybe (LoopBox a b)
leftSlide (LB anf) =
    case headTail anf of
        Left _ -> Nothing
        Right (HT s ss) -> case s of
            s1 :***: s2 -> case isId s2 of
                -- If it's Id, you cannot slide further -- the removeId and compTwoCompose in leftExtract
                -- should mean that there being Id here => can't slide something useful in that slot.
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