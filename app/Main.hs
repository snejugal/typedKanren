{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Core
import Goal
import DeriveLogic
import UnifiableBase ()

import GHC.Generics (Generic)

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
main = do
  mapM_ print $ extract' <$> take 10 (run treeo)
