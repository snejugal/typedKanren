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

import Control.Lens (Prism, from)
import Control.Lens.TH (makePrisms)
import Data.Function ((&))
import Data.Tagged (Tagged)
import GHC.Exts (IsList, IsString (..))
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

instance IsString SExpr where
  fromString = SSymbol . Atomic

makeLogic ''SExpr
makePrisms ''LogicSExpr

_LogicSSymbol'
  :: Prism
      (Tagged (s, n, c, l) LogicSExpr)
      (Tagged (s', n, c, l) LogicSExpr)
      (Tagged s (Term Symbol))
      (Tagged s' (Term Symbol))
_LogicSSymbol' = from _Tagged . _LogicSSymbol . _Tagged

_LogicSNil'
  :: Prism
      (Tagged (s, n, c, l) LogicSExpr)
      (Tagged (s, n', c, l) LogicSExpr)
      (Tagged n ())
      (Tagged n' ())
_LogicSNil' = from _Tagged . _LogicSNil . _Tagged

_LogicSCons'
  :: Prism
      (Tagged (s, n, c, l) LogicSExpr)
      (Tagged (s, n, c', l) LogicSExpr)
      (Tagged c (Term SExpr, Term SExpr))
      (Tagged c' (Term SExpr, Term SExpr))
_LogicSCons' = from _Tagged . _LogicSCons . _Tagged

_LogicSClosure'
  :: Prism
      (Tagged (s, n, c, l) LogicSExpr)
      (Tagged (s, n, c, l') LogicSExpr)
      (Tagged l (Term Symbol, Term SExpr, Term Env))
      (Tagged l' (Term Symbol, Term SExpr, Term Env))
_LogicSClosure' = from _Tagged . _LogicSClosure . _Tagged

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

notClosureo :: Term SExpr -> Goal ()
notClosureo =
  matche'
    & on' _LogicSClosure' (const failo)
    & on' _LogicSSymbol' (\_ -> successo ())
    & on' _LogicSNil' successo
    & on' _LogicSCons' (\_ -> successo ())
    & enter'

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

properListo :: Term SExpr -> Term Env -> Term SExpr -> Goal ()
properListo exprs env value = exprs & (matche'
  & on' _LogicSNil' (\() -> value === Value LogicSNil)
  & on' _LogicSCons' (\(car, cdr) -> do
      (car', cdr') <- fresh
      value === Value (LogicSCons car' cdr')
      evalo car env car'
      properListo cdr env cdr')
  & on' _LogicSSymbol' (const failo)
  & on' _LogicSClosure' (const failo)
  & enter')
{- FOURMOLU_ENABLE -}

evalo :: Term SExpr -> Term Env -> Term SExpr -> Goal ()
evalo expr env value =
  disjMany
    [ do
        quoteo value expr
        notClosureo value
        notInEnvo quote env
    , do
        exprs <- fresh
        listo exprs expr
        properListo exprs env value
    , do
        x <- fresh
        expr === Value (LogicSSymbol x)
        lookupo x env value
    , do
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
    ]
