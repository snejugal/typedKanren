{-# LANGUAGE TypeApplications #-}

module Matche (example, eithero') where

import Data.Function ((&))
import Data.Tagged (Tagged)

import Control.Lens (Prism, from)
import Core
import Goal
import LogicalBase
import Match

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

_LogicLeft'
  :: Prism
      (Tagged (l, r) (LogicEither a b))
      (Tagged (l', r) (LogicEither a' b))
      (Tagged l (Term a))
      (Tagged l' (Term a'))
_LogicLeft' = from _Tagged . _LogicLeft . _Tagged

_LogicRight'
  :: Prism
      (Tagged (l, r) (LogicEither a b))
      (Tagged (l, r') (LogicEither a b'))
      (Tagged r (Term b))
      (Tagged r' (Term b'))
_LogicRight' = from _Tagged . _LogicRight . _Tagged

eithero' :: (Logical a, Logical b) => Term (Either a b) -> Goal ()
eithero' =
  matche'
    & on' _LogicLeft' (\_ -> return ())
    & on' _LogicRight' (\_ -> return ())
    & enter'

nestedo' :: Term (Either (Either Int Bool) Int) -> Goal ()
nestedo' =
  matche'
    & on' (_LogicLeft' . _Value' . _LogicLeft') (=== 42)
    & on' (_LogicLeft' . _Value' . _LogicRight') (=== Value True)
    & on' _LogicRight' (=== 1729)
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
