{-# LANGUAGE StandaloneKindSignatures, DataKinds, PolyKinds, RankNTypes,
    FlexibleContexts #-}

module NF where

-- * Data types and constructors

type Desc :: * -> *
data Desc x where
    V :: a -> Desc a
    P :: Desc a -> Desc b -> Desc (a,b)

type Val :: forall s. Desc s -> *
data Val x where
    One :: a -> Val (V a)
    Pair :: Val a -> Val b -> Val (P a b)

type ANF :: forall s s'. Desc s -> Desc s' -> *
data ANF x y where
    Loop :: Loop c => NoLoop (P a c) (P b c) -> ANF a b
    WithoutLoop :: NoLoop a b -> ANF a b

infixl 1 :>>>:
type NoLoop :: forall s s'. Desc s -> Desc s' -> *
data NoLoop x y where
    (:>>>:) :: NoLoop a b -> NoComp b c -> NoLoop a c
    WithoutComp :: NoComp a b -> NoLoop a b

infixl 3 :***:
type NoComp :: forall s s'. Desc s -> Desc s' -> *
data NoComp x y where
    (:***:) :: NoComp a b -> NoComp a' b' -> NoComp (P a a') (P b b')
    Arr :: (Val a -> Val b) -> NoComp a b
    Pre :: Val a -> NoComp a a
    Id :: NoComp a a
    Squish :: NoComp (P a (P b c)) (P b (P a c))
    Assoc :: NoComp (P (P a b) c) (P a (P b c))
    Cossa :: NoComp (P a (P b c)) (P (P a b) c)
    Juggle :: NoComp (P (P a b) c) (P (P a c) b)
    Distribute :: NoComp (P (P a b) (P c d)) (P (P a c) (P b d))

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
    show Squish = "Squish"
    show Assoc = "Assoc"
    show Cossa = "Cossa"
    show Juggle = "Juggle"
    show Distribute = "Distribute"

-- * Eq instances

instance Eq a => Eq (Val (V a)) where
    One a == One b = a == b

instance (Eq (Val a), Eq (Val b)) => Eq (Val (P a b)) where
    Pair a b == Pair a' b' = a == a' && b == b'

-- * Loop resolution

-- TODO: try to generalise these to laziness in general (needed for Assoc).
-- Alternatively, try to naturally convert to Yampa somehow??

-- This is a workaround!
-- If you just write (Pair b c, f') = runArrowAST f (Pair a c), it forces
-- strict evaluation because it doesn't know which constructor will be used
-- by c. As such, we provide instances which identify the constructor for it.
-- (No, I'm still confused too.)
-- This means that we can run ArrowAST/ArrowNF programs to test their
-- equivalence, although we won't need this in the final implementation since
-- we no longer need laziness at that point.
-- TODO: Use TemplateHaskell to generate these instances.
class Loop c where
    loops ::
        forall s s'
        (a :: Desc s) (b :: Desc s') (arr :: forall t t'. Desc t -> Desc t' -> *).
        (Val (P a c) -> (Val (P b c), arr (P a c) (P b c)))
        -> Val a -> (Val b, arr (P a c) (P b c))

instance forall (a :: *). Loop (V a) where
    loops f a =
        let (Pair b (One c), f') = f (Pair a (One c)) in (b, f')

instance forall (a :: *) (b :: *). Loop (P (V a) (V b)) where
    loops f a =
        let (Pair b (Pair (One c) (One d)), f')
                = f (Pair a (Pair (One c) (One d)))
        in (b, f')

instance forall (a :: *) (b :: *) (c :: *).
    Loop (P (V a) (P (V b) (V c))) where
        loops f a =
            let (Pair b (Pair (One c) (Pair (One d) (One e))), f')
                    = f (Pair a (Pair (One c) (Pair (One d) (One e))))
            in (b, f')

instance forall (a :: *) (b :: *) (c :: *).
    Loop (P (P (V a) (V b)) (V c)) where
        loops f a =
            let (Pair b (Pair (Pair (One c) (One d)) (One e)), f')
                    = f (Pair a (Pair (Pair (One c) (One d)) (One e)))
            in (b, f')

-- NOTE: THIS INSTANCE IS DELIBERATELY INCORRECT
-- This has the same infinite loop problems as were caused by just stating
-- (Pair b c, f') = runArrowAST f (Pair a c).
-- We include the above instances so we can test program equivalence -
-- this instance is to make sure that other programs are still writable,
-- since in the final loopPre-style implementation you won't need to execute
-- loop like this at all.
instance {-# OVERLAPPABLE #-} forall s (c :: Desc s). Loop c where
    loops f a = let (Pair b c, f') = f (Pair a c) in (b, f')

-- * Running functions

debug :: ANF a b -> String
debug = show

runANF :: ANF a b -> Val a -> (Val b, ANF a b)
runANF (Loop f) a = let (b, cont) = loops (runNoLoop f) a in (b, Loop cont)
runANF (WithoutLoop f) a = let (b, cont) = runNoLoop f a in (b, WithoutLoop cont)

runNoLoop :: NoLoop a b -> Val a -> (Val b, NoLoop a b)
runNoLoop (f :>>>: g) a =
    let (intermediate, f') = runNoLoop f a
        (final, g') = runNoComp g intermediate
    in (final, f' :>>>: g')
runNoLoop (WithoutComp f) a = let (b, cont) = runNoComp f a in (b, WithoutComp cont)

runNoComp :: NoComp a b -> Val a -> (Val b, NoComp a b)
runNoComp (f :***: g) (Pair a b) =
    let (l, f') = runNoComp f a
        (r, g') = runNoComp g b
    in (Pair l r, f' :***: g')
runNoComp (Arr f) a = (f a, Arr f)
runNoComp (Pre i) a = (i, Pre a)
runNoComp Id a = (a, Id)
runNoComp Squish (Pair a (Pair b c)) = (Pair b (Pair a c), Squish)
runNoComp Assoc (Pair (Pair a b) c) = (Pair a (Pair b c), Assoc)
runNoComp Cossa (Pair a (Pair b c)) = (Pair (Pair a b) c, Cossa)
runNoComp Juggle (Pair (Pair a b) c) = (Pair (Pair a c) b, Juggle)
runNoComp Distribute (Pair (Pair a b) (Pair c d)) =
    (Pair (Pair a c) (Pair b d), Distribute)