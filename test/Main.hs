module Main (main) where

import System.Exit (exitFailure, exitSuccess)

import qualified CoreTests
import qualified GoalTests
import qualified THTests

main :: IO ()
main = do
  good <-
    and
      <$> sequence
        [ CoreTests.runTests
        , THTests.runTests
        , GoalTests.runTests
        ]
  if good
    then exitSuccess
    else exitFailure
