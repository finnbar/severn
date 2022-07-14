module NF where

-- * Data types and constructors

data ANF a b where
    Loop :: NoLoop (a,c) (b,c) -> ANF a b
    WithoutLoop :: NoLoop a b -> ANF a b

infixl 1 :>>>:
data NoLoop a b where
    (:>>>:) :: NoLoop a b -> NoComp b c -> NoLoop a c
    WithoutComp :: NoComp a b -> NoLoop a b

infixl 3 :***:
data NoComp a b where
    (:***:) :: NoComp a b -> NoComp a' b' -> NoComp (a,a') (b,b')
    Arr :: (a -> b) -> NoComp a b
    Pre :: a -> NoComp a a
    Id :: NoComp a a

lift_ :: NoComp a b -> NoLoop a b
lift_ = WithoutComp

arr_ :: (a -> b) -> NoLoop a b
arr_ = WithoutComp . Arr

id_ :: NoLoop a a
id_ = WithoutComp Id

pre_ :: a -> NoLoop a a
pre_ = WithoutComp . Pre

-- * Show instances

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

-- * Running functions

debug :: ANF a b -> String
debug = show

runANF :: ANF a b -> a -> (b, ANF a b)
runANF (Loop f) a = let ((b, c), cont) = runNoLoop f (a, c) in (b, Loop cont)
runANF (WithoutLoop f) a = let (b, cont) = runNoLoop f a in (b, WithoutLoop cont)

runNoLoop :: NoLoop a b -> a -> (b, NoLoop a b)
runNoLoop (f :>>>: g) a =
    let (intermediate, f') = runNoLoop f a
        (final, g') = runNoComp g intermediate
    in (final, f' :>>>: g')
runNoLoop (WithoutComp f) a = let (b, cont) = runNoComp f a in (b, WithoutComp cont)

runNoComp :: NoComp a b -> a -> (b, NoComp a b)
runNoComp (f :***: g) (a, b) =
    let (l, f') = runNoComp f a
        (r, g') = runNoComp g b
    in ((l, r), f' :***: g')
runNoComp (Arr f) a = (f a, Arr f)
runNoComp (Pre i) a = (i, Pre a)
runNoComp Id a = (a, Id)