import Test.Tasty

import ArrowCFSFSpec
import TransformSpec

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [arrowCFSFSpec, transformSpec]
