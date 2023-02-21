import Test.Tasty

import ArrowCFSpec
import TransformSpec

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [arrowCFSpec, transformSpec]
