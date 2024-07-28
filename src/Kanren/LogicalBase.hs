{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Logical representations for some @base@ types along with their (orphan)
-- 'Logical' instances.
module Kanren.LogicalBase (
  -- * Primitive types

  -- | There are 'Logical' instances for 'Bool', 'Char', 'Int', and 'Void'. They
  -- don't require a separate logic representation.

  -- ** Prisms for 'Bool'
  _False,
  _True,
  _False',
  _True',

  -- * Tuples

  -- | For tuples, the logical representation is a tuple too, so they don't need a
  -- separate logic type. Currently, there's a 'Logical' instance for 2-tuples
  -- only.

  -- * Lists
  LogicList (..),

  -- ** Prisms for lists
  _LogicNil,
  _LogicCons,
  _LogicNil',
  _LogicCons',

  -- * 'Maybe'
  LogicMaybe (..),

  -- ** Prisms for 'Maybe'
  _LogicNothing,
  _LogicJust,
  _LogicNothing',
  _LogicJust',

  -- * 'Either'
  LogicEither (..),

  -- ** Prisms for 'Either'
  _LogicLeft,
  _LogicRight,
  _LogicLeft',
  _LogicRight',
) where

import Control.Lens.TH (makePrisms)
import Data.Void (Void)
import GHC.Exts (IsList (..))
import GHC.Generics (Generic)

import Control.DeepSeq (NFData)
import Kanren.Core
import Kanren.GenericLogical
import Kanren.TH (makeExhaustivePrisms, makeLogical)

instance Logical Int
instance Logical Char
instance Logical Void

instance Logical Bool
makePrisms ''Bool
makeExhaustivePrisms ''Bool

instance (Logical a, Logical b) => Logical (a, b) where
  type Logic s (a, b) = (Term s a, Term s b)
  unify = genericUnify
  walk = genericWalk
  occursCheck = genericOccursCheck
  inject = genericInject
  extract = genericExtract

data LogicList s a
  = LogicNil
  | LogicCons (Term s a) (Term s [a])
  deriving (Generic)
deriving instance (Eq (Logic s a)) => Eq (LogicList s a)
deriving instance (NFData (Logic s a)) => NFData (LogicList s a)

-- | This instance tries to print the list as a regular one. In case the tail is
-- unknown, the list is printed as @[...|_.n]@, like in Prolog.
instance (Show (Logic s a)) => Show (LogicList s a) where
  showsPrec _ LogicNil s = "[]" ++ s
  showsPrec _ (LogicCons x xs) s = '[' : shows x (show' xs)
   where
    show' (Var var) = '|' : shows var (']' : s)
    show' (Value LogicNil) = ']' : s
    show' (Value (LogicCons y ys)) = ',' : shows y (show' ys)

instance (Logical a) => Logical [a] where
  type Logic s [a] = LogicList s a
  unify = genericUnify
  walk = genericWalk
  occursCheck = genericOccursCheck
  inject = genericInject
  extract = genericExtract

instance IsList (LogicList s a) where
  type Item (LogicList s a) = Term s a
  fromList [] = LogicNil
  fromList (x : xs) = LogicCons x (Value (fromList xs))
  toList LogicNil = []
  toList (LogicCons x xs) = x : toList xs -- NOTE: toList for (Term s [a]) is partial

makePrisms ''LogicList
makeExhaustivePrisms ''LogicList

makeLogical ''Maybe
makePrisms ''LogicMaybe
makeExhaustivePrisms ''LogicMaybe
deriving instance (Eq (Logic s a)) => Eq (LogicMaybe s a)
deriving instance (Show (Logic s a)) => Show (LogicMaybe s a)

makeLogical ''Either
makePrisms ''LogicEither
makeExhaustivePrisms ''LogicEither
deriving instance (Eq (Logic s a), Eq (Logic s b)) => Eq (LogicEither s a b)
deriving instance (Show (Logic s a), Show (Logic s b)) => Show (LogicEither s a b)
