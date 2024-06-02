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
  deriving (Eq, Generic)

instance Show SExpr where
  show (SSymbol (Atomic symbol)) = symbol
  show SNil = "()"
  show (SCons car cdr) = "(" ++ show car ++ showSList cdr
  show (SClosure (Atomic var) body env) =
    "#(lambda (" ++ var ++ ") " ++ show body ++ " " ++ show env ++ ")"

showSList :: SExpr -> [Char]
showSList SNil = ")"
showSList (SCons car cdr) = " " ++ show car ++ showSList cdr
showSList other = " . " ++ show other ++ ")"

instance IsList SExpr where
  type Item SExpr = SExpr
  fromList [] = SNil
  fromList (x : xs) = SCons x (fromList xs)
  toList = undefined

makeLogic ''SExpr

instance Show LogicSExpr where
  show (LogicSSymbol (Value (Atomic symbol))) = symbol
  show (LogicSSymbol var) = show var
  show LogicSNil = "()"
  show (LogicSCons car cdr) = "(" ++ show car ++ showLogicSList cdr
  show (LogicSClosure var body env) =
    "#(lambda (" ++ show var ++ ") " ++ show body ++ " " ++ show env ++ ")"

showLogicSList :: Term SExpr -> [Char]
showLogicSList (Value LogicSNil) = ")"
showLogicSList (Value (LogicSCons car cdr)) = " " ++ show car ++ showLogicSList cdr
showLogicSList other = " . " ++ show other ++ ")"

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
              var =/= expectedVar
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
        entryVar =/= var
        notInEnvo var rest)
    & enter'
{- FOURMOLU_ENABLE -}

evalo :: Term SExpr -> Term Env -> Term SExpr -> Goal ()
evalo expr env value =
  disjMany
    [ do
        x <- fresh
        expr === Value (LogicSSymbol x)
        lookupo x env value
    , do
        (x, body) <- fresh
        lambdao x body expr
        value === Value (LogicSClosure x body env)
        notInEnvo lambda env
    , do
        (rator, rand) <- fresh
        applyo rator rand expr

        (x, body, ratorEnv) <- fresh
        evalo rator env (Value (LogicSClosure x body ratorEnv))
        rand' <- fresh
        evalo rand env rand'

        evalo body (Value (LogicCons (Value (x, rand')) ratorEnv)) value
    ]
