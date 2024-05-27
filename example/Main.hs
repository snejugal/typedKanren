module Main (main) where

import qualified Binary
import qualified Lists
import qualified Matche
import qualified Trees

main :: IO ()
main = do
  Lists.example

  putStrLn ""
  Trees.example

  putStrLn ""
  Matche.example

  putStrLn ""
  Binary.example
