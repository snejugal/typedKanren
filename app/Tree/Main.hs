{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import GHC.Generics (Generic)
import Control.Lens.TH (makePrisms)
import Data.Function ((&))

import Core
import Goal
import DeriveLogic
import UnifiableBase ()
import Match

data Tree a = Empty | Node a (Tree a) (Tree a)
  deriving (Show, Generic)
deriveLogic ''Tree
makePrisms ''LogicTree

treeo :: ValueOrVar (Tree Int) -> Goal ()
treeo = matche
  & on _LogicEmpty return
  & on _LogicNode (\(value, left, right) -> do
      value === 0
      treeo left
      treeo right)

main :: IO ()
main = mapM_ print $ extract' <$> take 10 (run treeo)
