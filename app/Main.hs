{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Main (main) where

import Lib
import GHC.Generics (Generic)

data Tree = Empty | Node Tree Tree
  deriving (Show, Generic)

data LogicTree = LEmpty | LNode (ValueOrVar Tree) (ValueOrVar Tree)
  deriving (Show, Generic)

instance Unifiable Tree where
  type Term Tree = LogicTree

  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

treeo :: ValueOrVar Tree -> Goal ()
treeo x = conde
  [ [x === Value LEmpty]
  , [ fresh $ \(left, right) -> do
        x === Value (LNode left right)
        treeo left
        treeo right
    ]
  ]

main :: IO ()
main = do
  mapM_ print $ extract' <$> take 10 (run treeo)
