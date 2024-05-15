{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Match (
  on,
  matche,
  _Value,
  on',
  matche',
  Exhausted,
  Initial,
  _Tagged,
  Value' (..),
  enter',
) where

import Control.Lens (Iso, Prism', from, iso, prism', review)
import Core
import Data.Tagged (Tagged (Tagged, unTagged))
import Data.Void (Void)
import Goal
import PrismA (PrismA (Source, make), reviewA)

on
  :: (Logical a, Fresh v)
  => Prism' (Logic a) v
  -> (v -> Goal x)
  -> (Term a -> Goal x)
  -> Term a
  -> Goal x
on p f g x = disj (g x) $ do
  vars <- fresh
  x === Value (review p vars)
  f vars

matche :: Term a -> Goal x
matche = const failo

_Value :: Prism' (Term a) (Logic a)
_Value = prism' Value $ \case
  Value x -> Just x
  Var _ -> Nothing

newtype Matched a m = Matched (Term a)

class Exhausted a
instance Exhausted Void
instance (Exhausted a, Exhausted b) => Exhausted (a, b)

class Initial a
instance Initial ()
instance (Initial a, Initial b) => Initial (a, b)

_Tagged :: Iso b b' (Tagged a b) (Tagged a' b')
_Tagged = iso Tagged unTagged

data Value' a = Value'

instance (l ~ Logic a) => PrismA (Value' a) (Tagged m l) (Tagged m' l) where
  type Source (Value' a) (Tagged m l) = Tagged m (Term a)
  make Value' = from _Tagged . _Value . _Tagged

enter' :: (Initial m) => (Matched a m -> Goal x) -> Term a -> Goal x
enter' f = f . Matched

on'
  :: forall v a m m' x p
   . ( Logical a
     , Fresh v
     , forall i. PrismA p (Tagged () v) (Tagged i v)
     , Source p (Tagged () v) ~ Tagged m (Logic a)
     , Source p (Tagged Void v) ~ Tagged m' (Logic a)
     )
  => p
  -> (v -> Goal x)
  -> (Matched a m' -> Goal x)
  -> Matched a m
  -> Goal x
on' p f g (Matched x) = disj (g (Matched x)) $ do
  vars <- fresh
  let Tagged value = reviewA p (Tagged @() vars)
  x === Value value
  f vars

matche' :: (Exhausted m) => Matched a m -> Goal x
matche' = const failo
