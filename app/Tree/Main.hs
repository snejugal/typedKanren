{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import GHC.Generics (Generic)

import Core
import Goal
import DeriveLogic
import UnifiableBase ()

data Tree a = Empty | Node a (Tree a) (Tree a)
  deriving (Show, Generic)
deriveLogic ''Tree

treeo :: ValueOrVar (Tree Int) -> Goal ()
treeo x = conde
  [ [x === Value LogicEmpty]
  , [ fresh $ \(left, right) -> do
        x === Value (LogicNode 0 left right)
        treeo left
        treeo right
    ]
  ]

main :: IO ()
main = mapM_ print $ extract' <$> take 10 (run treeo)
