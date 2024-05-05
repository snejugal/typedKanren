{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE TupleSections #-}

module Match (on, matche, on', matche', Exhausted, Biprism, biprism) where

import Core
import Goal
import Control.Lens ( Prism', review, Choice (right'), Profunctor (dimap) )
import Data.Void (Void)
import Data.Biapplicative (Biapplicative (bipure, (<<*>>)), Bifunctor (first, bimap))
import Data.Tagged (Tagged(Tagged, unTagged))
import Data.Functor.Const (Const(Const, getConst))

on :: (Unifiable s, Fresh a)
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

type Biprism s t a b = forall p f. (Choice p, Biapplicative f) =>
  p a (f a b) -> p s (f s t)

biprism :: (a -> s) -> (b -> t) -> (s -> Either t a) -> Biprism s t a b
biprism setl setr get = dimap get' set' . right'
  where
    get' x = first (x,) (get x)
    set' (Right fab) = bimap setl setr fab
    set' (Left (s, t)) = bipure s t

reviewl :: Biprism s t a b -> a -> s
reviewl p = getConst . unTagged . p . Tagged . Const

-- reviewr :: Biprism s t a b -> b -> t
-- reviewr p = unTagged . unTagged . p . Tagged . Tagged

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

class Exhausted a

instance Exhausted Void
instance (Exhausted a, Exhausted b) => Exhausted (Either a b)

on' :: (Unifiable s, Fresh a)
    => Biprism (Term s) (Term t) a (ValueOrVar Void) -- fixme: exactly one variable basically
    -> (a -> Goal x)
    -> (ValueOrVar t -> Goal x)
    -> ValueOrVar s
    -> Goal x
on' p f g x =
  case x of
    Var (VarId varId) -> disj otherArms thisArm
      where
        otherArms = g (Var (VarId varId))
        thisArm = fresh $ \vars -> do
          x === Value (reviewl p vars)
          f vars
    Value value -> case matching p value of
      Right a -> f a
      Left other -> g (Value other)

matche' :: Exhausted a => ValueOrVar a -> Goal x
matche' = const failo
