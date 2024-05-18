module Main (main) where

import qualified CoreTests
import System.Exit (exitFailure, exitSuccess)
import qualified THTests

main :: IO ()
main = do
  good <- and <$> sequence [CoreTests.runTests, THTests.runTests]
  if good
    then exitSuccess
    else exitFailure
