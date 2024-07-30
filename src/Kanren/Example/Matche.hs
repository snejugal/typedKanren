{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Kanren.Example.Matche (example, eithero') where

import Control.Lens.TH
import Control.Monad.ST (runST)
import Data.Bifunctor (bimap)
import Data.Function ((&))
import GHC.Generics (Generic)

import Kanren.Core
import Kanren.Goal
import Kanren.LogicalBase
import Kanren.Match
import Kanren.TH

eithero :: (Logical a, Logical b) => Term s (Either a b) -> Goal s ()
eithero =
  matche
    & on _LogicLeft (\_ -> return ())
    & on _LogicRight (\_ -> return ())

nestedo :: Term s (Either (Either Int Bool) Int) -> Goal s ()
nestedo =
  matche
    & on (_LogicLeft . _Value . _LogicLeft) (=== 42)
    & on (_LogicLeft . _Value . _LogicRight) (=== inject' True)
    & on _LogicRight (=== 1729)

-- Exhaustive pattern-matching

eithero' :: (Logical a, Logical b) => Term s (Either a b) -> Goal s ()
eithero' =
  matche'
    & on' _LogicLeft' (\_ -> return ())
    & on' _LogicRight' (\_ -> return ())
    & enter'

nestedo' :: Term s (Either (Either Int Bool) Int) -> Goal s ()
nestedo' =
  matche'
    & on' (_LogicLeft' . _Value' . _LogicLeft') (=== 42)
    & on' (_LogicLeft' . _Value' . _LogicRight') (=== inject' True)
    & on' _LogicRight' (=== 1729)
    & enter'

data Nat
  = Z
  | S Nat
  deriving (Show, Generic)

makeLogical ''Nat
makePrisms ''LogicNat
makeExhaustivePrisms ''LogicNat

_Z' :: ExhaustivePrism (LogicNat st) (z, s) (z', s) () z z'
_Z' = _LogicZ'
_S' :: ExhaustivePrism (LogicNat st) (z, s) (z, s') (Term st Nat) s s'
_S' = _LogicS'

natToInto :: Term s Nat -> Term s Int -> Goal s ()
natToInto nat int =
  nat
    & ( matche'
          & on' _Z' (\() -> int === 0)
          & on' (_S' . _Value' . _Z') (\() -> int === 1)
          & on' (_S' . _Value' . _S' . _Value' . _Z') (\() -> int === 2)
          & on' (_S' . _Value' . _S' . _Value' . _S') (const failo) -- give up
          & enter'
      )

example :: IO ()
example = do
  putStrLn "eithero:"
  mapM_ putStrLn $ runST (map show <$> run' (eithero @Int @Bool))

  putStrLn "\neithero':"
  mapM_ putStrLn $ runST (map show <$> run' (eithero' @Int @Bool))

  putStrLn "\nnestedo:"
  mapM_ print $ runST (fmap extract' <$> run' nestedo)

  putStrLn "\nnestedo':"
  mapM_ print $ runST (fmap extract' <$> run' nestedo')

  putStrLn "\nnatToInto:"
  mapM_ print $ runST (fmap (bimap extract' extract') <$> run' (uncurry natToInto))
