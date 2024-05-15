{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Matche (example) where

import Control.Lens.Prism (prism)
import Data.Function ((&))
import Data.Tagged (Tagged (Tagged))

import Core
import Goal
import LogicalBase
import Match
import PrismA

eithero :: (Logical a, Logical b) => Term (Either a b) -> Goal ()
eithero =
  matche
    & on _LogicLeft (\_ -> return ())
    & on _LogicRight (\_ -> return ())

nestedo :: Term (Either (Either Int Bool) Int) -> Goal ()
nestedo =
  matche
    & on (_LogicLeft . _Value . _LogicLeft) (=== 42)
    & on (_LogicLeft . _Value . _LogicRight) (=== Value True)
    & on _LogicRight (=== 1729)

-- Exhaustive pattern-matching

type instance InitMatch (Either a b) = ((), ())

data LogicLeft' r b = LogicLeft'
data LogicRight' l a = LogicRight'

instance (l ~ ()) => PrismA (LogicLeft' r b) (l, Term a) (l', Term a') where
  type Source (LogicLeft' r b) (l, Term a) = Tagged (l, r) (LogicEither a b)
  make LogicLeft' = prism (\(_, a) -> Tagged (LogicLeft a)) $ \case
    (Tagged (LogicLeft a)) -> Right ((), a)
    (Tagged (LogicRight b)) -> Left (Tagged (LogicRight b))

instance (r ~ ()) => PrismA (LogicRight' l a) (r, Term b) (r', Term b') where
  type Source (LogicRight' l a) (r, Term b) = Tagged (l, r) (LogicEither a b)
  make LogicRight' = prism (\(_, b) -> Tagged (LogicRight b)) $ \case
    (Tagged (LogicRight b)) -> Right ((), b)
    (Tagged (LogicLeft a)) -> Left (Tagged (LogicLeft a))

eithero' :: forall a b. (Logical a, Logical b) => Term (Either a b) -> Goal ()
eithero' =
  matche'
    & on' LogicLeft' (\(_ :: Term a) -> return ())
    & on' LogicRight' (\(_ :: Term b) -> return ())
    & enter'

example :: IO ()
example = do
  putStrLn "eithero:"
  mapM_ print $ run (eithero @Int @Bool)

  putStrLn "\neithero':"
  mapM_ print $ run (eithero' @Int @Bool)

  putStrLn "\nnestedo:"
  mapM_ print $ extract' <$> run nestedo
