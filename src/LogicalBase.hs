{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module LogicalBase where

import GHC.Exts (IsList (..))
import GHC.Generics

import Control.Lens (Prism, Prism', prism)
import Control.Lens.TH (makePrisms)
import Core
import Data.Void (Void)
import DeriveLogic
import GenericLogical

deriveLogic ''Either
makePrisms ''LogicEither

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

deriving instance (Show (Logic a)) => Show (LogicList a)

instance (Logical a) => Logical [a] where
  type Logic [a] = LogicList a
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

instance IsList (LogicList a) where
  type Item (LogicList a) = ValueOrVar a
  fromList [] = LogicNil
  fromList (x : xs) = LogicCons x (Value (fromList xs))

instance (Logical a, Logical b) => Logical (a, b) where
  type Logic (a, b) = (ValueOrVar a, ValueOrVar b)
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

instance Logical Int
instance Logical Bool
instance Logical Void
