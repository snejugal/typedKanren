{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Kanren.Data.Scheme (
  Symbol,
  Env,
  SExpr (..),
  LogicSExpr (..),
  Value (..),
  LogicValue (..),
  evalo,
) where

import Control.Lens (Prism, from)
import Control.Lens.TH (makePrisms)
import Data.Function ((&))
import Data.Tagged (Tagged)
import GHC.Exts (IsList, IsString (..))
import GHC.Generics (Generic)
import GHC.IsList (IsList (..))

import Control.DeepSeq
import Kanren.Core
import Kanren.Goal
import Kanren.LogicalBase
import Kanren.Match
import Kanren.TH

type Symbol = Atomic String
type Env = [(Symbol, Value)]

data SExpr
  = SSymbol Symbol
  | SNil
  | SCons SExpr SExpr
  deriving (Eq, Generic, NFData)

data Value
  = SExpr SExpr
  | Closure Symbol SExpr Env
  deriving (Eq, Generic, NFData)

instance Show SExpr where
  show (SSymbol (Atomic symbol)) = symbol
  show SNil = "()"
  show (SCons car cdr) = "(" ++ show car ++ showSList cdr

showSList :: SExpr -> [Char]
showSList SNil = ")"
showSList (SCons car cdr) = " " ++ show car ++ showSList cdr
showSList other = " . " ++ show other ++ ")"

instance Show Value where
  show (SExpr expr) = show expr
  show (Closure (Atomic var) body env) =
    "#(lambda (" ++ var ++ ") " ++ show body ++ " " ++ show env ++ ")"

instance IsList SExpr where
  type Item SExpr = SExpr
  fromList [] = SNil
  fromList (x : xs) = SCons x (fromList xs)
  toList = undefined

instance IsString SExpr where
  fromString = SSymbol . Atomic

makeLogic ''SExpr
makeLogic ''Value
makePrisms ''LogicSExpr
makePrisms ''LogicValue

deriving instance NFData LogicSExpr

_LogicSSymbol'
  :: Prism
      (Tagged (s, n, c) LogicSExpr)
      (Tagged (s', n, c) LogicSExpr)
      (Tagged s (Term Symbol))
      (Tagged s' (Term Symbol))
_LogicSSymbol' = from _Tagged . _LogicSSymbol . _Tagged

_LogicSNil'
  :: Prism
      (Tagged (s, n, c) LogicSExpr)
      (Tagged (s, n', c) LogicSExpr)
      (Tagged n ())
      (Tagged n' ())
_LogicSNil' = from _Tagged . _LogicSNil . _Tagged

_LogicSCons'
  :: Prism
      (Tagged (s, n, c) LogicSExpr)
      (Tagged (s, n, c') LogicSExpr)
      (Tagged c (Term SExpr, Term SExpr))
      (Tagged c' (Term SExpr, Term SExpr))
_LogicSCons' = from _Tagged . _LogicSCons . _Tagged

instance Show LogicSExpr where
  show (LogicSSymbol (Value (Atomic symbol))) = symbol
  show (LogicSSymbol var) = show var
  show LogicSNil = "()"
  show (LogicSCons car cdr) = "(" ++ show car ++ showLogicSList cdr

instance Show LogicValue where
  show (LogicSExpr expr) = show expr
  show (LogicClosure var body env) =
    "#(lambda (" ++ show var ++ ") " ++ show body ++ " " ++ show env ++ ")"

showLogicSList :: Term SExpr -> [Char]
showLogicSList (Value LogicSNil) = ")"
showLogicSList (Value (LogicSCons car cdr)) = " " ++ show car ++ showLogicSList cdr
showLogicSList other = " . " ++ show other ++ ")"

applyo :: Term SExpr -> Term SExpr -> Term SExpr -> Goal ()
applyo f x expr = expr === Value (LogicSCons f (Value (LogicSCons x (Value LogicSNil))))

lambda :: Term Symbol
lambda = inject' (Atomic "lambda")

quote :: Term Symbol
quote = inject' (Atomic "quote")

list :: Term Symbol
list = inject' (Atomic "list")

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

quoteo :: Term SExpr -> Term SExpr -> Goal ()
quoteo value expr =
  expr
    === Value
      ( LogicSCons
          (Value (LogicSSymbol quote))
          (Value (LogicSCons value (Value LogicSNil)))
      )

listo :: Term SExpr -> Term SExpr -> Goal ()
listo exprs expr =
  expr === Value (LogicSCons (Value (LogicSSymbol list)) exprs)

{- FOURMOLU_DISABLE -}
lookupo :: Term Symbol -> Term Env -> Term Value -> Goal ()
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

properListo :: Term SExpr -> Term Env -> Term SExpr -> Goal ()
properListo exprs env value = exprs & (matche'
  & on' _LogicSNil' (\() -> value === Value LogicSNil)
  & on' _LogicSCons' (\(car, cdr) -> do
      (car', cdr') <- fresh
      value === Value (LogicSCons car' cdr')
      evalo car env (Value (LogicSExpr car'))
      properListo cdr env cdr')
  & on' _LogicSSymbol' (const failo)
  & enter')
{- FOURMOLU_ENABLE -}

evalo :: Term SExpr -> Term Env -> Term Value -> Goal ()
evalo expr env value =
  disjMany
    [ do
        arg <- fresh
        quoteo arg expr
        notInEnvo quote env
        value === Value (LogicSExpr arg)
    , do
        (exprs, value') <- fresh
        listo exprs expr
        value === Value (LogicSExpr value')
        properListo exprs env value'
    , do
        x <- fresh
        expr === Value (LogicSSymbol x)
        lookupo x env value
    , do
        (x, body) <- fresh
        lambdao x body expr
        value === Value (LogicClosure x body env)
        notInEnvo lambda env
    , do
        (rator, rand) <- fresh
        applyo rator rand expr

        (x, body, ratorEnv) <- fresh
        evalo rator env (Value (LogicClosure x body ratorEnv))
        rand' <- fresh
        evalo rand env rand'

        evalo body (Value (LogicCons (Value (x, rand')) ratorEnv)) value
    ]
