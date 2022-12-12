import Test.Tasty

import ArrowNFSpec
import TransformSpec

-- TODO: Give our tests better descriptions.
-- use testPropertyNamed "human-readable" "prop_name" prop_name

main :: IO ()
main = do
    !res <- mapM checkSequential [arrowNFSpec, transformSpec]
    unless (and res) exitFailure
