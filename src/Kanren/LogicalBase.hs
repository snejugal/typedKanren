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

import Control.Lens (Prism, from)
import Control.Lens.TH (makePrisms)
import Data.Tagged (Tagged)
import Data.Void (Void)
import GHC.Exts (IsList (..))
import GHC.Generics (Generic)

import Control.DeepSeq (NFData)
import Kanren.Core
import Kanren.GenericLogical
import Kanren.Match (_Tagged)
import Kanren.TH (makeLogical)

instance Logical Int
instance Logical Char
instance Logical Void

instance Logical Bool
makePrisms ''Bool

_False'
  :: Prism
      (Tagged (false, true) Bool)
      (Tagged (false', true) Bool)
      (Tagged false ())
      (Tagged false' ())
_False' = from _Tagged . _False . _Tagged

_True'
  :: Prism
      (Tagged (false, true) Bool)
      (Tagged (false, true') Bool)
      (Tagged true ())
      (Tagged true' ())
_True' = from _Tagged . _True . _Tagged

instance (Logical a, Logical b) => Logical (a, b) where
  type Logic (a, b) = (Term a, Term b)
  unify = genericUnify
  walk = genericWalk
  occursCheck = genericOccursCheck
  inject = genericInject
  extract = genericExtract

data LogicList a
  = LogicNil
  | LogicCons (Term a) (Term [a])
  deriving (Generic)
deriving instance (Eq (Logic a)) => Eq (LogicList a)
deriving instance (NFData (Logic a)) => NFData (LogicList a)

-- | This instance tries to print the list as a regular one. In case the tail is
-- unknown, the list is printed as @[...|_.n]@, like in Prolog.
instance (Show (Logic a)) => Show (LogicList a) where
  showsPrec _ LogicNil s = "[]" ++ s
  showsPrec _ (LogicCons x xs) s = '[' : shows x (show' xs)
   where
    show' (Var var) = '|' : shows var (']' : s)
    show' (Value LogicNil) = ']' : s
    show' (Value (LogicCons y ys)) = ',' : shows y (show' ys)

instance (Logical a) => Logical [a] where
  type Logic [a] = LogicList a
  unify = genericUnify
  walk = genericWalk
  occursCheck = genericOccursCheck
  inject = genericInject
  extract = genericExtract

instance IsList (LogicList a) where
  type Item (LogicList a) = Term a
  fromList [] = LogicNil
  fromList (x : xs) = LogicCons x (Value (fromList xs))
  toList LogicNil = []
  toList (LogicCons x xs) = x : toList xs -- NOTE: toList for (Term [a]) is partial

makePrisms ''LogicList

_LogicNil'
  :: Prism
      (Tagged (nil, cons) (LogicList a))
      (Tagged (nil', cons) (LogicList a))
      (Tagged nil ())
      (Tagged nil' ())
_LogicNil' = from _Tagged . _LogicNil . _Tagged

_LogicCons'
  :: Prism
      (Tagged (nil, cons) (LogicList a))
      (Tagged (nil, cons') (LogicList a'))
      (Tagged cons (Term a, Term [a]))
      (Tagged cons' (Term a', Term [a']))
_LogicCons' = from _Tagged . _LogicCons . _Tagged

makeLogical ''Maybe
makePrisms ''LogicMaybe
deriving instance (Eq (Logic a)) => Eq (LogicMaybe a)
deriving instance (Show (Logic a)) => Show (LogicMaybe a)

_LogicNothing'
  :: Prism
      (Tagged (nothing, just) (LogicMaybe a))
      (Tagged (nothing', just) (LogicMaybe a))
      (Tagged nothing ())
      (Tagged nothing' ())
_LogicNothing' = from _Tagged . _LogicNothing . _Tagged

_LogicJust'
  :: Prism
      (Tagged (nothing, just) (LogicMaybe a))
      (Tagged (nothing, just') (LogicMaybe a'))
      (Tagged just (Term a))
      (Tagged just' (Term a'))
_LogicJust' = from _Tagged . _LogicJust . _Tagged

makeLogical ''Either
makePrisms ''LogicEither
deriving instance (Eq (Logic a), Eq (Logic b)) => Eq (LogicEither a b)
deriving instance (Show (Logic a), Show (Logic b)) => Show (LogicEither a b)

_LogicLeft'
  :: Prism
      (Tagged (left, right) (LogicEither a b))
      (Tagged (left', right) (LogicEither a' b))
      (Tagged left (Term a))
      (Tagged left' (Term a'))
_LogicLeft' = from _Tagged . _LogicLeft . _Tagged

_LogicRight'
  :: Prism
      (Tagged (left, right) (LogicEither a b))
      (Tagged (left, right') (LogicEither a b'))
      (Tagged right (Term b))
      (Tagged right' (Term b'))
_LogicRight' = from _Tagged . _LogicRight . _Tagged
