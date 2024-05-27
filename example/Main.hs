module Main (main) where

import qualified Kanren.Data.Binary as Binary
import qualified Kanren.Example.List as List
import qualified Kanren.Example.Matche as Matche
import qualified Kanren.Example.Tree as Tree

main :: IO ()
main = do
  List.example

  putStrLn ""
  Tree.example

  putStrLn ""
  Matche.example

  putStrLn ""
  Binary.example
