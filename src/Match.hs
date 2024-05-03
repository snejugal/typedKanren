{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Match (on, matche) where

import Core
import UnifiableBase ()
import Goal
import Control.Lens ( Prism', review )

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
