{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Matche (example) where

import Control.Lens.TH (makePrisms)
import Data.Function ((&))

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

data LogicEither' l r a b
  = LogicLeft' l (Term a)
  | LogicRight' r (Term b)
makePrisms ''LogicEither'

data LogicLeft'' r b = LogicLeft''
data LogicRight'' l a = LogicRight''

instance PrismA (LogicLeft'' r b) (l, Term a) (l', Term a') where
  type Source (LogicLeft'' r b) (l, Term a) = LogicEither' l r a b
  make LogicLeft'' = _LogicLeft'

instance PrismA (LogicRight'' l a) (r, Term b) (l', Term b') where
  type Source (LogicRight'' l a) (r, Term b) = LogicEither' l r a b
  make LogicRight'' = _LogicRight'

instance (Logical a, Logical b) => Matchable (Either a b) (l, r) where
  type Matched (Either a b) (l, r) = LogicEither' l r a b
  type Initial (Either a b) = ((), ())

  enter (LogicLeft a) = LogicLeft' () a
  enter (LogicRight b) = LogicRight' () b

  back (LogicLeft' _ a) = LogicLeft a
  back (LogicRight' _ b) = LogicRight b

instance (Exhausted l, Exhausted r) => Exhausted (LogicEither' l r a b) where
  exhausted (LogicLeft' l _) = exhausted l
  exhausted (LogicRight' r _) = exhausted r

eithero' :: forall a b. (Logical a, Logical b) => Term (Either a b) -> Goal ()
eithero' =
  matche'
    & on' LogicLeft'' (\(_ :: Term a) -> return ())
    & on' LogicRight'' (\(_ :: Term b) -> return ())
    & enter'

example :: IO ()
example = do
  putStrLn "eithero:"
  mapM_ print $ run (eithero @Int @Bool)

  putStrLn "\neithero':"
  mapM_ print $ run (eithero' @Int @Bool)

  putStrLn "\nnestedo:"
  mapM_ print $ extract' <$> run nestedo
