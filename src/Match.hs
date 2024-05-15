{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Match (on, matche, _Value, on', matche', Exhausted, InitMatch, enter') where

import Control.Lens (Prism', prism', review)
import Core
import Data.Tagged (Tagged (Tagged))
import Data.Void (Void)
import Goal
import PrismA (PrismA (Source), matchingA, reviewA)

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

type family InitMatch a
newtype Matched a m = Matched (Term a)

class Exhausted a
instance Exhausted Void
instance (Exhausted a, Exhausted b) => Exhausted (a, b)

enter' :: (Matched a (InitMatch a) -> Goal x) -> Term a -> Goal x
enter' f = f . Matched

on'
  :: forall v a m m' x p
   . ( Logical a
     , Fresh v
     , forall i. PrismA p ((), v) (i, v)
     , Source p ((), v) ~ Tagged m (Logic a)
     , Source p (Void, v) ~ Tagged m' (Logic a)
     )
  => p
  -> (v -> Goal x)
  -> (Matched a m' -> Goal x)
  -> Matched a m
  -> Goal x
on' p f g (Matched x@(Var varId)) = disj otherArms thisArm
   where
    otherArms = g (Matched x)
    thisArm = do
      vars <- fresh
      let Tagged value = reviewA p ((), vars)
      Var varId === Value value
      f vars
on' p f g (Matched x@(Value value)) =
  case matchingA @((), v) @(Void, v) p (Tagged value) of
    Right (_, a) -> f a
    Left _ -> g (Matched x)

matche' :: (Exhausted m) => Matched a m -> Goal x
matche' = const failo
