{-# LANGUAGE ScopedTypeVariables, TypeOperators #-}

module Transform where

import ArrowNF
import Data.Maybe (fromJust)
import Control.Applicative
import Data.Type.Equality (type (:~~:)(..))

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
transformLoop lb = fromJust $ transformLoopM lb <|> transformLoopD lb

transformLoopM :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (ANF a b)
transformLoopM (LB anf) = transformLoopM' id_ anf 
    where
        -- Inputs: the part of the ANF already checked and the part to check
        transformLoopM' :: (ValidDesc a, ValidDesc b, ValidDesc c, ValidDesc d) =>
            ANF (P a c) d -> ANF d (P b c) -> Maybe (ANF a b)
        transformLoopM' before anf =
            case headTail (leftCrunch anf) of
                -- If this anf consists of only one term, see if it is decoupled.
                Left d -> asDecoupled d >>= \d' -> Just . Single . Dec $ LoopM before d' id_
                -- If not, see if the head is currently decoupled.
                Right (HT s ss) -> case asDecoupled s of
                    Just sdec -> Just . Single . Dec $ LoopM before sdec ss
                    -- If it isn't decoupled, use left extract to remove the bits that can't
                    -- be part of the solution.
                    Nothing -> case compTwoCompose $ leftExtract s of
                        nodec :>>>: dec -> transformLoopM' (before >>> nodec) (dec >>> ss)
                        Single s' -> transformLoopM' (before >>> Single s') ss

transformLoopD :: (ValidDesc a, ValidDesc b) => LoopBox a b -> Maybe (ANF a b)
transformLoopD lb =
    case sliding leftSlide lb of
        Right anf -> Just anf
        Left lb' -> case sliding rightSlide lb' of
            Right anf -> Just anf
            Left _ -> Nothing
    where
        sliding :: (ValidDesc a, ValidDesc b) =>
            (LoopBox a b -> Maybe (LoopBox a b)) -> LoopBox a b -> Either (LoopBox a b) (ANF a b)
        sliding slide lb = case isLoopD lb of
            Just anf -> Right anf
            Nothing -> case slide lb of
                Just lb' -> sliding slide lb'
                Nothing -> Left lb

-- If this is in the form of a LoopD, make it so.
-- Also apply left/right tightening.
isLoopD :: ValidDesc a => LoopBox a b -> Maybe (ANF a b)
isLoopD (LB anf) = case initLast anf of
    Left (f :***: g) ->
        asDecoupled g >>= Just . tightening (Single f *** id_)
    Right (IL ss (f :***: g)) ->
        asDecoupled g >>= Just . tightening (ss >>> (Single f *** id_))
    _ -> Nothing

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
        rightTighten (TG l anf r dec) = case initLast (rightCrunch anf) of
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
        leftTighten (TG l anf r dec) = case headTail (leftCrunch anf) of
            Right (HT (f :***: g) ss) ->
                -- Check we're not trying to slide id, because that will go infinite (see rightTighten).
                case isId f of
                    Just HRefl -> TG l anf r dec
                    Nothing -> leftTighten (TG (l >>> Single f) (Single (idNoComp :***: g) >>> ss) r dec)
            _ -> TG l anf r dec

-- Move all non-ID terms to the left.
leftCrunch :: ANF a b -> ANF a b
leftCrunch anf = case initLast anf of
    Left _ -> anf
    Right (IL an f) -> case initLast an of
        Left an' -> compTwoCompose $ leftFill (C2 an' f)
        Right (IL a n) ->
            leftCrunch' a $ leftFill (C2 n f)
    where
        leftCrunch' :: ValidDesc a => ANF a b -> CompTwo b c -> ANF a c
        leftCrunch' a (C2 n' f') = leftCrunch (a >>> Single n') >>> Single f'

-- Move all non-ID terms to the right.
rightCrunch :: ANF a b -> ANF a b
rightCrunch anf = case headTail anf of
    Left _ -> anf
    Right (HT a nf) -> case headTail nf of
        Left nf' -> compTwoCompose $ rightFill (C2 a nf')
        Right (HT n f) ->
            rightCrunch' (rightFill (C2 a n)) f
    where
        rightCrunch' :: ValidDesc c => CompTwo a b -> ANF b c -> ANF a c
        rightCrunch' (C2 a' n') f = Single a' >>> rightCrunch (Single n' >>> f)

-- Apply right extract to the input term, returning a composition
rightExtract :: (ValidDesc a, ValidDesc b) => NoComp a b -> CompTwo a b
rightExtract (Dec d) = C2 (Dec d) idNoComp
rightExtract (f :***: g) = compTwoPar (rightExtract f) (rightExtract g)
rightExtract f = C2 idNoComp f

-- Apply left extract to the input term, returning a composition
leftExtract :: (ValidDesc a, ValidDesc b) => NoComp a b -> CompTwo a b
leftExtract (Dec d) = C2 idNoComp (Dec d)
leftExtract (f :***: g) = compTwoPar (leftExtract f) (leftExtract g)
leftExtract f = C2 f idNoComp

-- Apply right fill to a composition, moving parts of the composition.
-- TODO: This is the opposite way around to the paper -- the paper gets it wrong.
rightFill :: CompTwo a b -> CompTwo a b
rightFill (C2 (f :***: g) (h :***: i)) =
    compTwoPar (rightFill $ C2 f h) (rightFill $ C2 g i)
rightFill (C2 f g) = case isId g of
    Just HRefl -> C2 idNoComp f
    Nothing -> C2 f g

-- Apply left fill to a composition, moving parts of the composition.
leftFill :: CompTwo a b -> CompTwo a b
leftFill (C2 (f :***: g) (h :***: i)) =
    compTwoPar (leftFill $ C2 f h) (leftFill $ C2 g i)
leftFill (C2 f g) = case isId f of
    Just HRefl -> C2 g idNoComp 
    Nothing -> C2 f g

asDecoupled :: NoComp a b -> Maybe (Decoupled a b)
asDecoupled (Dec d) = Just d
asDecoupled (f :***: g) = do
    fd <- asDecoupled f
    gd <- asDecoupled g
    return $ BothDec fd gd
asDecoupled _ = Nothing

-- The process for leftSlide is more complex than rightSlide, since we need to make a pre on the right side.
-- 1. Right extract on the first term to get pre >>> nonpre.
-- 2. Slide pre to the left.
-- 3. Right fill on the last term to combine any pre that were on the last term with those in the new last term.
-- 4. Left fill on the first term to fill the gaps left in nonpre. (TODO Is this needed?)
leftSlide :: ValidDesc b => LoopBox a b -> Maybe (LoopBox a b)
leftSlide lb = doLeftFill . doRightFill <$> (doRightExtract lb >>= doLeftSlide)
    where
        doRightExtract :: LoopBox a b -> Maybe (LoopBox a b)
        doRightExtract (LB anf) = case headTail anf of
            Left _ -> Nothing
            Right (HT s ss) -> case s of
                s1 :***: s2 -> Just $ LB $ (Single s1 *** compTwoCompose (rightExtract s2)) >>> ss
                _ -> Nothing
        doRightFill :: LoopBox a b -> LoopBox a b
        doRightFill (LB anf) = case initLast anf of
            Left nc -> LB anf
            Right (IL st u) -> case initLast st of
                Left st' -> LB $ compTwoCompose (rightFill $ C2 st' u)
                Right (IL s t) -> LB $ s >>> compTwoCompose (rightFill $ C2 t u)
        doLeftFill :: LoopBox a b -> LoopBox a b
        doLeftFill (LB anf) = case headTail anf of
            Left nc -> LB anf
            Right (HT s tu) -> case headTail tu of
                Left tu' -> LB $ compTwoCompose (leftFill $ C2 s tu')
                Right (HT t u) -> LB $ compTwoCompose (leftFill $ C2 s t) >>> u
        doLeftSlide :: ValidDesc b => LoopBox a b -> Maybe (LoopBox a b)
        doLeftSlide (LB anf) = case headTail anf of
            Left _ -> Nothing
            Right (HT s ss) -> case s of
                s1 :***: s2 -> case isId s2 of
                    -- If it's Id, you cannot slide further -- the removeId and compTwoCompose in leftExtract
                    -- should mean that there being Id here => can't slide something useful in that slot.
                    Just HRefl -> Nothing
                    Nothing -> Just $ LB $ (Single s1 *** id_) >>> ss >>> (id_ *** Single s2)
                -- impossible to slide
                _ -> Nothing

-- The process is as follows:
-- 1. Get the term next to the second output of the loop body, and split it into pre >>> nonpre using right extract.
-- 2. Right slide the nonpre, since it will not help.
-- 3. Use right fill to fill in any gaps in pre with parts of the term before it.
rightSlide :: ValidDesc a => LoopBox a b -> Maybe (LoopBox a b)
rightSlide lb = doRightFill <$> (doRightExtract lb >>= doRightSlide)
    where
        doRightExtract :: LoopBox a b -> Maybe (LoopBox a b)
        doRightExtract (LB anf) = case initLast anf of
            Left _ -> Nothing
            Right (IL ss s) -> case s of
                s1 :***: s2 -> Just $ LB $ ss >>> (Single s1 *** compTwoCompose (rightExtract s2))
                _ -> Nothing
        doRightFill :: LoopBox a b -> LoopBox a b
        doRightFill (LB anf) = case initLast anf of
            Left nc -> LB anf
            Right (IL st u) -> case initLast st of
                Left st' -> LB $ compTwoCompose (rightFill $ C2 st' u)
                Right (IL s t) -> LB $ s >>> compTwoCompose (rightFill $ C2 t u)
        doRightSlide :: ValidDesc a => LoopBox a b -> Maybe (LoopBox a b)
        doRightSlide (LB anf) = case initLast anf of
            Left _ -> Nothing
            Right (IL ss s) -> case s of
                s1 :***: s2 -> case isId s2 of
                    Just HRefl -> Nothing
                    Nothing -> Just $ LB $ (id_ *** Single s2) >>> ss >>> (Single s1 *** id_)
                _ -> Nothing