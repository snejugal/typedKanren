{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Matche (example, eithero') where

import Data.Function ((&))
import Data.Tagged (Tagged (Tagged, unTagged))

import Control.Lens (Iso, from, iso)
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

data LogicLeft' r b = LogicLeft'
data LogicRight' l a = LogicRight'

_Tagged :: Iso b b' (Tagged a b) (Tagged a' b')
_Tagged = iso Tagged unTagged

instance PrismA (LogicLeft' r b) (Tagged l (Term a)) (Tagged l' (Term a')) where
  type Source (LogicLeft' r b) (Tagged l (Term a)) = Tagged (l, r) (LogicEither a b)
  make LogicLeft' = from _Tagged . _LogicLeft . _Tagged

instance PrismA (LogicRight' l a) (Tagged r (Term b)) (Tagged r' (Term b')) where
  type Source (LogicRight' l a) (Tagged r (Term b)) = Tagged (l, r) (LogicEither a b)
  make LogicRight' = from _Tagged . _LogicRight . _Tagged

eithero' :: forall a b. (Logical a, Logical b) => Term (Either a b) -> Goal ()
eithero' =
  matche'
    & on' LogicLeft' (\(_ :: Term a) -> failo)
    & on' LogicRight' (\(_ :: Term b) -> return ())
    & enter'

nestedo' :: Term (Either (Either Int Bool) Int) -> Goal ()
nestedo' =
  matche'
    & on' (LogicLeft' :. Value' :. LogicLeft') (=== 42)
    & on' (LogicLeft' :. Value' :. LogicRight') (=== Value True)
    & on' LogicRight' (=== 1729)
    & enter'

example :: IO ()
example = do
  putStrLn "eithero:"
  mapM_ print $ run (eithero @Int @Bool)

  putStrLn "\neithero':"
  mapM_ print $ run (eithero' @Int @Bool)

  putStrLn "\nnestedo:"
  mapM_ print $ extract' <$> run nestedo

  putStrLn "\nnestedo':"
  mapM_ print $ extract' <$> run nestedo'
