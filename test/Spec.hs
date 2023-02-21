import Test.Tasty

import ArrowCFSpec
import TransformSpec

-- TODO: Give our tests better descriptions.
-- use testPropertyNamed "human-readable" "prop_name" prop_name

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [arrowCFSpec, transformSpec]
