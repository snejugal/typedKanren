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
import GenericLogical
import TH (makeLogic)

makeLogic ''Maybe
makePrisms ''LogicMaybe
deriving instance (Eq (Logic a)) => Eq (LogicMaybe a)
deriving instance (Show (Logic a)) => Show (LogicMaybe a)

makeLogic ''Either
makePrisms ''LogicEither
deriving instance (Eq (Logic a), Eq (Logic b)) => Eq (LogicEither a b)
deriving instance (Show (Logic a), Show (Logic b)) => Show (LogicEither a b)

data LogicList a
  = LogicNil
  | LogicCons (Term a) (Term [a])
  deriving (Generic)

deriving instance (Eq (Term a)) => Eq (LogicList a)

_LogicNil :: Prism' (LogicList a) ()
_LogicNil = prism (const LogicNil) $ \case
  LogicNil -> Right ()
  LogicCons x xs -> Left (LogicCons x xs)

_LogicCons :: Prism (LogicList a) (LogicList b) (Term a, Term [a]) (Term b, Term [b])
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
  type Item (LogicList a) = Term a
  fromList [] = LogicNil
  fromList (x : xs) = LogicCons x (Value (fromList xs))

instance (Logical a, Logical b) => Logical (a, b) where
  type Logic (a, b) = (Term a, Term b)
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

instance Logical Int
instance Logical Char
instance Logical Void

instance Logical Bool
makePrisms ''Bool
