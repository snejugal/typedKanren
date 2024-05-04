{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Match (on, matche, on', matche', Exhausted) where

import Core
import Goal
import Control.Lens ( Prism', review, Iso, withIso )
import Data.Void (Void)

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

class Exhausted a

instance Exhausted Void
instance (Exhausted a, Exhausted b) => Exhausted (Either a b)

on' :: (Unifiable s, Fresh a)
    => Iso (Term s) (Term s) (Either (Term t) a) a
    -> (a -> Goal x)
    -> (ValueOrVar t -> Goal x)
    -> ValueOrVar s
    -> Goal x
on' p f g x = withIso p $ \to back ->
  case x of
    Var (VarId varId) -> disj otherArms thisArm
      where
        otherArms = g (Var (VarId varId))
        thisArm = fresh $ \vars -> do
          x === Value (back vars)
          f vars
    Value value -> case to value of
      Right a -> f a
      Left other -> g (Value other)

matche' :: Exhausted a => ValueOrVar a -> Goal x
matche' = const failo
