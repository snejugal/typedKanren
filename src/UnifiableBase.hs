{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

module UnifiableBase where

import GHC.Exts (IsList(..))
import GHC.Generics

import Core
import Goal
import GenericUnifiable
import Control.Lens (Prism, Prism', prism)

data LogicList a
  = LogicNil
  | LogicCons (ValueOrVar a) (ValueOrVar [a])
  deriving (Generic)

_LogicNil :: Prism' (LogicList a) ()
_LogicNil = prism (const LogicNil) $ \case
  LogicNil -> Right ()
  LogicCons x xs -> Left (LogicCons x xs)

_LogicCons :: Prism (LogicList a) (LogicList b) (ValueOrVar a, ValueOrVar [a]) (ValueOrVar b, ValueOrVar [b])
_LogicCons = prism (uncurry LogicCons) $ \case
  LogicCons x xs -> Right (x, xs)
  LogicNil -> Left LogicNil

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
