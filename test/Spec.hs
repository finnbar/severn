{-# LANGUAGE TemplateHaskell #-}

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import SpecTH

import ArrowAST (AAST)
import qualified ArrowAST as AAST
import ArrowNF (ANF, ArrowPre(..))
import qualified ArrowNF as ANF
import Transform (ALP)
import qualified Transform as T

import System.Exit (exitFailure)
import Control.Monad
import Control.Arrow

-- TODO: Clean this up into two files

-- * Test ANF vs reference implementation.

checkEqual :: (Eq b, Show b) => (AAST a b, ANF a b) -> [a] -> PropertyT IO ()
checkEqual _ [] = return ()
checkEqual (aast, anf) (a:as) = do
    let (b, aast') = AAST.runAAST aast a
        (b', anf') = ANF.runANF anf a
    b === b'
    checkEqual (aast', anf') as

-- Basic check that `arr` works like in the reference implementation.
prop_check_arr_matches :: Property
prop_check_arr_matches = property $ do
    inps <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    let progs = $(dup [| arr (+1) |])
    checkEqual progs inps

-- Check that a simple loop works like the reference implementation.
prop_simple_loop :: Property
prop_simple_loop = property $ do
    inps <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    let progs = $(dup [| loop (arr (\(a,b) -> (a+b, a)) >>> second (pre 0)) |])
    checkEqual progs inps

-- Check that `***` works like the reference implementation.
prop_par :: Property
prop_par = property $ do
    inpsl <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    inpsr <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    let inps = zip inpsl inpsr
        progs = $(dup [| arr (+1) *** arr (+2) |])
    checkEqual progs inps

-- Check that (f >>> g) *** (h >>> i) works. This is relevant because our
-- implementation transforms this to (f *** h) >>> (g *** i).
prop_distribute :: Property
prop_distribute = property $ do
    inpsl <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    inpsr <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    let inps = zip inpsl inpsr
        progs = $(dup [| (arr (+1) >>> arr (+2)) *** (arr (+3) >>> arr (+4)) |])
    checkEqual progs inps

-- Check that the above also works with `pre` (which updates internal state).
prop_distribute_pre :: Property
prop_distribute_pre = property $ do
    inpsl <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    inpsr <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    let inps = zip inpsl inpsr
        progs = $(dup [| (arr (+1) >>> pre 0) *** (pre 0 >>> arr (+4)) |])
    checkEqual progs inps

-- Check that `first` and `second` work accordingly.
prop_first_second :: Property
prop_first_second = property $ do
    inpsl <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    inpsr <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    let inps = zip inpsl inpsr
        progs = $(dup [| first (arr (+1)) >>> second (arr (+2)) |])
    checkEqual progs inps

-- Check that a loop inside a loop works.
prop_loop_in_loop :: Property
prop_loop_in_loop = property $ do
    inps <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    let progs = $(dup
            [| loop (loop (arr (\((a,c),b) -> ((a+b, c), a)) >>> second (pre 0)) >>> second (pre 0)) |])
    checkEqual progs inps

-- Checks that a composition of loops, where neither loop affects the other, works.
prop_loop_in_loop_composed :: Property
prop_loop_in_loop_composed = property $ do
    inps <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    let progs = $(dup
            [| loop (first (loop (arr (\(a,b) -> (a+b, a)) >>> second (pre 0)))
                >>> second (loop (arr (\(a,b) -> (a+b, a)) >>> second (pre 0)))
                >>> second (pre 0)) |])
    checkEqual progs inps

-- Checks that a composition of loops, where the result of one is used in the other, works.
prop_loop_in_loop_related :: Property
prop_loop_in_loop_related = property $ do
    inps <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    let progs = $(dup
            [| loop (first (loop (arr (\(a,b) -> (a+b, a)) >>> second (pre 0)))
                >>> arr (uncurry (+))
                >>> loop (arr (\(a,b) -> (a+b, a)) >>> second (pre 0))
                >>> arr (\x -> (x,x))
                >>> second (pre 0)) |])
    checkEqual progs inps

-- * Test `transform`.

checkEqual' :: (Eq b, Show b) => (ANF a b, ALP a b) -> [a] -> PropertyT IO ()
checkEqual' _ [] = return ()
checkEqual' (anf, alp) (a:as) = do
    let (b, anf') = ANF.runANF anf a
        (b', alp') = T.runALP alp a
    b === b'
    checkEqual' (anf', alp') as

complexNoLoop :: ANF Int Int
complexNoLoop = arr (+2) >>> arr (\x -> (x,x)) >>> arr (uncurry (+))

prop_transform_noloop :: Property
prop_transform_noloop = property $ do
    inps <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    checkEqual' (complexNoLoop, T.transform complexNoLoop) inps

prop_transform_rightslide :: Property 
prop_transform_rightslide = property $ do
    inps <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    delay <- forAll $ Gen.int (Range.linear 0 1000)
    let prog = loop (arr (\(x,y) -> (x+y,x)) >>> second (pre delay) >>> second complexNoLoop)
    checkEqual' (prog, T.transform prog) inps

{-
TODO: Add test for complex routing -- i.e. the reason we need squashRight.
Then find out why bigpre test isn't working.

prop_transform_complexrouting :: Property
prop_transform_complexrouting = property $ do
    inps <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    delay <- forAll $ Gen.int (Range.linear 0 1000)
    undefined

prop_transform_bigpre :: Property
prop_transform_bigpre = property $ do
    inps <- forAll $ Gen.list (Range.linear 5 20) $ Gen.int (Range.linear 0 1000)
    delay <- forAll $ Gen.int (Range.linear 0 1000)
    delay' <- forAll $ Gen.int (Range.linear 0 1000)
    let prog = loop (arr (\(x,y) -> (x+y,x)) >>> pre (delay, delay') >>> second complexNoLoop)
    checkEqual' (prog, T.transform prog) inps
-}

main :: IO ()
main = do
    res <- checkSequential $$(discover)
    unless res exitFailure