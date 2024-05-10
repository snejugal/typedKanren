{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Main (main) where

import Control.Lens.TH (makePrisms)
import Data.Function ((&))
import GHC.Generics (Generic)

import Core
import Goal
import LogicalBase ()
import Match
import TH (makeLogic)

data Tree a = Empty | Node a (Tree a) (Tree a)
  deriving (Show, Generic)
makeLogic ''Tree
makePrisms ''LogicTree

treeo :: Term (Tree Int) -> Goal ()
treeo =
  matche
    & on _LogicEmpty return
    & on
      _LogicNode
      ( \(value, left, right) -> do
          value === 0
          treeo left
          treeo right
      )

inverto :: (Logical a) => Term (Tree a) -> Term (Tree a) -> Goal ()
inverto tree inverted =
  tree
    & ( matche
          & on _LogicEmpty (\() -> inverted === Value LogicEmpty)
          & on
            _LogicNode
            ( \(value, left, right) -> do
                (invertedLeft, invertedRight) <- fresh
                inverted === Value (LogicNode value invertedLeft invertedRight)
                inverto left invertedRight
                inverto right invertedLeft
            )
      )

trees :: [Term (Tree Int)]
trees = run treeo

--    4
--  2   6
-- 1 3 5 7
example :: Tree Int
example =
  Node
    4
    (Node 2 (leaf 1) (leaf 3))
    (Node 6 (leaf 5) (leaf 7))
 where
  leaf x = Node x Empty Empty

main :: IO ()
main = do
  putStrLn "trees:"
  mapM_ print $ extract' <$> take 10 (run treeo)

  putStrLn "inverto example:"
  mapM_ print $ extract' <$> run (inverto (inject' example))
