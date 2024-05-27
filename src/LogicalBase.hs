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

import Control.Lens (Prism, Prism', from, prism)
import Control.Lens.TH (makePrisms)
import Data.Tagged (Tagged)
import Data.Void (Void)
import GHC.Exts (IsList (..))
import GHC.Generics (Generic)

import Core
import GenericLogical
import Match (_Tagged)
import TH (makeLogic)

makeLogic ''Maybe
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
      (Tagged (nothing, just') (LogicMaybe a))
      (Tagged just (Term a))
      (Tagged just' (Term a))
_LogicJust' = from _Tagged . _LogicJust . _Tagged

makeLogic ''Either
makePrisms ''LogicEither
deriving instance (Eq (Logic a), Eq (Logic b)) => Eq (LogicEither a b)
deriving instance (Show (Logic a), Show (Logic b)) => Show (LogicEither a b)

_LogicLeft'
  :: Prism
      (Tagged (left, right) (LogicEither a b))
      (Tagged (left', right) (LogicEither a b))
      (Tagged left (Term a))
      (Tagged left' (Term a))
_LogicLeft' = from _Tagged . _LogicLeft . _Tagged

_LogicRight'
  :: Prism
      (Tagged (left, right) (LogicEither a b))
      (Tagged (left, right') (LogicEither a b))
      (Tagged right (Term b))
      (Tagged right' (Term b))
_LogicRight' = from _Tagged . _LogicRight . _Tagged

data LogicList a
  = LogicNil
  | LogicCons (Term a) (Term [a])
  deriving (Generic)

deriving instance (Eq (Term a)) => Eq (LogicList a)
deriving instance (Show (Term a)) => Show (LogicList a)

instance (Logical a) => Logical [a] where
  type Logic [a] = LogicList a
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

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
