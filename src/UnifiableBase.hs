{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module UnifiableBase where

import GHC.Exts (IsList(..))
import GHC.Generics

import Core
import Goal
import GenericUnifiable

data LogicList a
  = LogicNil
  | LogicCons (ValueOrVar a) (ValueOrVar [a])
  deriving (Generic)

deriving instance (Show (Term a)) => Show (LogicList a)

instance Unifiable a => Unifiable [a] where
  type Term [a] = LogicList a
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

instance IsList (LogicList a) where
  type Item (LogicList a) = ValueOrVar a
  fromList [] = LogicNil
  fromList (x:xs) = LogicCons x (Value (fromList xs))

instance Unifiable Int
instance Unifiable Bool

instance (Unifiable a, Unifiable b) => UnifiableFresh (a, b) where
  fresh = genericFresh

instance (Unifiable a) => UnifiableFresh [a] where
  fresh = genericFresh
