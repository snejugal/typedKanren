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

module Match (on, matche, _Value, on', matche', Exhausted (..), Matchable (..), enter') where

import Control.Lens (Prism', prism', review)
import Core
import Data.Void (Void, absurd)
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

class Exhausted a where
  exhausted :: a -> x

instance Exhausted Void where
  exhausted = absurd

on'
  :: forall v a m m' x p
   . ( Matchable a m
     , Fresh v
     , forall i. PrismA p ((), v) (i, v)
     , Source p ((), v) ~ Matched a m
     , Source p (Void, v) ~ Matched a m'
     )
  => p
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
      let value = back (reviewA p ((), vars))
      Var varId === Value value
      f vars
  Value' value -> case matchingA @((), v) @(Void, v) p value of
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
