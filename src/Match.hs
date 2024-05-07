{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Match (on, matche, on', matche', Exhausted (..), Matchable (..), enter', Biprism, biprism) where

import Control.Lens (Choice (right'), Prism', Profunctor (dimap), review)
import Core
import Data.Biapplicative (Biapplicative (bipure, (<<*>>)), Bifunctor (bimap, first))
import Data.Functor.Const (Const (Const, getConst))
import Data.Tagged (Tagged (Tagged, unTagged))
import Data.Void (Void, absurd)
import Goal

on
  :: (Logical s, Fresh a)
  => Prism' (Term s) a
  -> (a -> Goal x)
  -> (ValueOrVar s -> Goal x)
  -> ValueOrVar s
  -> Goal x
on p f g x = disj (g x) thisArm
 where
  thisArm = case x of
    Var _ -> fresh $ \vars -> do
      x === Value (review p vars)
      f vars
    Value value -> case p Left value of
      Left a -> f a
      Right _ -> failo

matche :: ValueOrVar a -> Goal x
matche = const failo

type Biprism s t a b =
  forall p f
   . (Choice p, Biapplicative f)
  => p a (f a b)
  -> p s (f s t)

biprism :: (a -> s) -> (b -> t) -> (s -> Either t a) -> Biprism s t a b
biprism setl setr get = dimap get' set' . right'
 where
  get' x = first (x,) (get x)
  set' (Right fab) = bimap setl setr fab
  set' (Left (s, t)) = bipure s t

reviewl :: Biprism s t a b -> a -> s
reviewl p = getConst . unTagged . p . Tagged . Const

newtype Either' a b c = Either' (Either a (b, c))

instance Functor (Either' a b) where
  fmap = bimap id

instance Bifunctor (Either' a) where
  bimap _ _ (Either' (Left a)) = Either' (Left a)
  bimap f g (Either' (Right bc)) = Either' (Right (bimap f g bc))

instance Biapplicative (Either' a) where
  bipure b c = Either' (Right (bipure b c))

  Either' (Left a) <<*>> _ = Either' (Left a)
  _ <<*>> Either' (Left a) = Either' (Left a)
  Either' (Right fg) <<*>> Either' (Right bc) = Either' (Right (fg <<*>> bc))

matching :: Biprism s t a b -> s -> Either t a
matching p x = case p (Either' . Left) x of
  Either' (Left a) -> Right a
  Either' (Right (_, t)) -> Left t

class Exhausted a where
  exhausted :: a -> x

instance Exhausted Void where
  exhausted = absurd

on'
  :: (Matchable a m, Fresh v)
  => Biprism (Matched a m) (Matched a m') ((), v) (Void, v)
  -> (v -> Goal x)
  -> (MatchedValueOrVar a m' -> Goal x)
  -> MatchedValueOrVar a m
  -> Goal x
on' p f g x = case x of
  Var' varId -> disj otherArms thisArm
   where
    otherArms = g (Var' varId)
    thisArm = fresh $ \vars -> do
      let value = back (reviewl p ((), vars))
      Var varId === Value value
      f vars
  Value' value -> case matching p value of
    Right (_, a) -> f a
    Left other -> g (Value' other)

matche' :: (Exhausted (Matched a m)) => MatchedValueOrVar a m -> Goal x
matche' (Value' value) = exhausted value
matche' (Var' _) = failo

data MatchedValueOrVar a m
  = Var' (VarId a)
  | Value' (Matched a m)

class (Logical a) => Matchable a m where
  type Matched a m = r | r -> a m
  type Initial a

  enter :: Term a -> Matched a (Initial a)
  back :: Matched a m -> Term a

enter'
  :: forall a x
   . (Matchable a (Initial a))
  => (MatchedValueOrVar a (Initial a) -> x)
  -> ValueOrVar a
  -> x
enter' f x = f x'
 where
  x' = case x of
    Var varId -> Var' varId
    Value value -> Value' (enter @a @(Initial a) value)
