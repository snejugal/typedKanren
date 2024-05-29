{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Kanren.Data.Scheme (
  Symbol,
  Env,
  SExpr (..),
  LogicSExpr (..),
  symbolo,
  evalo,
) where

import Data.Function ((&))
import GHC.Exts (IsList)
import GHC.Generics (Generic)
import GHC.IsList (IsList (..))

import Kanren.Core
import Kanren.Goal
import Kanren.LogicalBase
import Kanren.Match
import Kanren.TH

type Symbol = Atomic String
type Env = [(Symbol, SExpr)]

data SExpr
  = SSymbol Symbol
  | SNil
  | SCons SExpr SExpr
  | SClosure Symbol SExpr Env
  deriving (Eq, Show, Generic)

instance IsList SExpr where
  type Item SExpr = SExpr
  fromList [] = SNil
  fromList (x : xs) = SCons x (fromList xs)
  toList = undefined

makeLogic ''SExpr
deriving instance Show LogicSExpr

symbolo :: Term SExpr -> Goal ()
symbolo value = do
  x <- fresh
  value === Value (LogicSSymbol x)

applyo :: Term SExpr -> Term SExpr -> Term SExpr -> Goal ()
applyo f x expr = expr === Value (LogicSCons f (Value (LogicSCons x (Value LogicSNil))))

lambda :: Term Symbol
lambda = inject' (Atomic "lambda")

lambdao :: Term Symbol -> Term SExpr -> Term SExpr -> Goal ()
lambdao x body expr =
  expr
    === Value
      ( LogicSCons
          (Value (LogicSSymbol lambda))
          ( Value
              ( LogicSCons
                  parameter
                  (Value (LogicSCons body (Value LogicSNil)))
              )
          )
      )
 where
  parameter = Value (LogicSCons (Value (LogicSSymbol x)) (Value LogicSNil))

{- FOURMOLU_DISABLE -}
lookupo :: Term Symbol -> Term Env -> Term SExpr -> Goal ()
lookupo expectedVar env returnValue =
  env & (matche'
    & on' _LogicNil' (const failo)
    & on' _LogicCons' (\(entry, rest) -> do
        (var, value) <- fresh
        entry === Value (var, value)
        disjMany
          [ do
              var === expectedVar
              value === returnValue
          , do
              -- var =/= expectedVar
              lookupo expectedVar rest returnValue
          ])
    & enter')

notInEnvo :: Term Symbol -> Term Env -> Goal ()
notInEnvo var =
  matche'
    & on' _LogicNil' successo
    & on' _LogicCons' (\(entry, rest) -> do
        (entryVar, value) <- fresh
        entry === Value (entryVar, value)
        -- entryVar =/= var
        notInEnvo var rest)
    & enter'
{- FOURMOLU_ENABLE -}

evalo :: Term SExpr -> Term Env -> Term SExpr -> Goal ()
evalo expr env value =
  disjMany
    [ do
        (rator, rand) <- fresh
        applyo rator rand expr

        (x, body, ratorEnv) <- fresh
        evalo rator env (Value (LogicSClosure x body ratorEnv))
        rand' <- fresh
        evalo rand env rand'

        evalo body (Value (LogicCons (Value (x, rand')) ratorEnv)) value
    , do
        (x, body) <- fresh
        lambdao x body expr
        value === Value (LogicSClosure x body env)
        notInEnvo lambda env
    , do
        x <- fresh
        expr === Value (LogicSSymbol x)
        lookupo x env value
    ]
