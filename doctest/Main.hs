-- | Check the @>>>@ examples in the Haddock comments of the library.
module Main (main) where

import Test.DocTest (doctest)

-- GHCi defaults to GHC2021, but the library is written in Haskell2010.
main :: IO ()
main = doctest ["-XHaskell2010", "-isrc", "src"]
