{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Match (on, matche, on', matche', Exhausted (..), Matchable (..), enter') where

import Biprism (Biprism, matching, reviewl)
import Control.Lens (Prism', review)
import Core
import Data.Void (Void, absurd)
import Goal

on
  :: (Logical a, Fresh v)
  => Prism' (Logic a) v
  -> (v -> Goal x)
  -> (Term a -> Goal x)
  -> Term a
  -> Goal x
on p f g x = disj (g x) thisArm
 where
  thisArm = case x of
    Var _ -> do
      vars <- fresh
      x === Value (review p vars)
      f vars
    Value value -> case p Left value of
      Left a -> f a
      Right _ -> failo

matche :: Term a -> Goal x
matche = const failo

class Exhausted a where
  exhausted :: a -> x

instance Exhausted Void where
  exhausted = absurd

on'
  :: (Matchable a m, Fresh v)
  => Biprism (Matched a m) (Matched a m') ((), v) (Void, v)
  -> (v -> Goal x)
  -> (MatchedTerm a m' -> Goal x)
  -> MatchedTerm a m
  -> Goal x
on' p f g x = case x of
  Var' varId -> disj otherArms thisArm
   where
    otherArms = g (Var' varId)
    thisArm = do
      vars <- fresh
      let value = back (reviewl p ((), vars))
      Var varId === Value value
      f vars
  Value' value -> case matching p value of
    Right (_, a) -> f a
    Left other -> g (Value' other)

matche' :: (Exhausted (Matched a m)) => MatchedTerm a m -> Goal x
matche' (Value' value) = exhausted value
matche' (Var' _) = failo

data MatchedTerm a m
  = Var' (VarId a)
  | Value' (Matched a m)

class (Logical a) => Matchable a m where
  type Matched a m = r | r -> a m
  type Initial a

  enter :: Logic a -> Matched a (Initial a)
  back :: Matched a m -> Logic a

enter'
  :: forall a x
   . (Matchable a (Initial a))
  => (MatchedTerm a (Initial a) -> x)
  -> Term a
  -> x
enter' f x = f x'
 where
  x' = case x of
    Var varId -> Var' varId
    Value value -> Value' (enter @a @(Initial a) value)
