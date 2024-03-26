{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Lib
import DeriveLogic

import GHC.Generics (Generic)

data Tree = Empty | Node Tree Tree
  deriving (Show, Generic)
deriveLogic ''Tree

treeo :: ValueOrVar Tree -> Goal ()
treeo x = conde
  [ [x === Value LogicEmpty]
  , [ fresh $ \(left, right) -> do
        x === Value (LogicNode left right)
        treeo left
        treeo right
    ]
  ]

main :: IO ()
main = do
  mapM_ print $ extract' <$> take 10 (run treeo)
