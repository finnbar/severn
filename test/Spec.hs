import Hedgehog

import ArrowNFSpec
import TransformSpec

import System.Exit (exitFailure)
import Control.Monad

main :: IO ()
main = do
    res <- and <$> mapM checkSequential [arrowNFSpec, transformSpec]
    unless res exitFailure