module Main (main) where

import qualified CoreTests
import System.Exit (exitSuccess, exitFailure)

main :: IO ()
main = do
  good <- and <$> sequence [CoreTests.runTests]
  if good
     then exitSuccess
     else exitFailure
