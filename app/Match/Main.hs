{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Lens (Prism, prism)
import Data.Function ((&))
import Data.Maybe (fromJust)
import Data.Void (Void)

import Core
import Goal
import LogicalBase
import Match
import PrismA

listo :: (Logical a) => Term [a] -> Goal ()
listo =
  matche
    & on _LogicNil return
    & on _LogicCons (\(_, xs) -> listo xs)

appendo :: (Logical a) => Term [a] -> Term [a] -> Term [a] -> Goal ()
appendo xs ys zs =
  xs
    & ( matche
          & on _LogicNil (\() -> ys === zs)
          & on
            _LogicCons
            ( \(x, xs') -> do
                zs' <- fresh
                zs === Value (LogicCons x zs')
                appendo xs' ys zs'
            )
      )

showLogicList :: (Show (Logic a)) => Term [a] -> String
showLogicList list = prefix ++ go list ++ suffix
 where
  (prefix, suffix) = case list of
    Value _ -> ("[", "]")
    _ -> ("", "")

  go (Var _) = "..?"
  go (Value LogicNil) = ""
  go (Value (LogicCons x xs)) = show x ++ sep ++ go xs
   where
    sep = case xs of
      Value LogicNil -> ""
      _ -> ", "

lists :: [Term [Int]]
lists = run listo

partitions :: [Int] -> [([Int], [Int])]
partitions xs = reifyBoth <$> run $ \(left, right) -> do
  appendo left right (inject' xs)
 where
  reifyBoth = fmap (\(a, b) -> (reify a, reify b))
  reify = fromJust . extract'

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

_LogicLeft' :: Prism (LogicEither' l r a b) (LogicEither' l' r a' b) (l, Term a) (l', Term a')
_LogicLeft' = prism (uncurry LogicLeft') $ \case
  LogicLeft' l a -> Right (l, a)
  LogicRight' r b -> Left (LogicRight' r b)

_LogicRight' :: Prism (LogicEither' l r a b) (LogicEither' l r' a b') (r, Term b) (r', Term b')
_LogicRight' = prism (uncurry LogicRight') $ \case
  LogicRight' r b -> Right (r, b)
  LogicLeft' l a -> Left (LogicLeft' l a)

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

eithero :: Term (Either Bool Int) -> Goal ()
eithero =
  matche'
    & on' LogicLeft'' (\x -> x === Value True)
    & on' LogicRight'' (\x -> x === Value 42)
    & enter'

data LogicList' n c a
  = LogicNil' n
  | LogicCons' c (Term a) (Term [a])

_LogicNil' :: Prism (LogicList' n c a) (LogicList' n' c a) (n, ()) (n', ())
_LogicNil' = prism (\(n, ()) -> LogicNil' n) $ \case
  LogicNil' n -> Right (n, ())
  LogicCons' c a as -> Left (LogicCons' c a as)

_LogicCons' :: Prism (LogicList' n c a) (LogicList' n c' a') (c, (Term a, Term [a])) (c', (Term a', Term [a']))
_LogicCons' = prism (\(c, (a, as)) -> LogicCons' c a as) $ \case
  LogicCons' c a s -> Right (c, (a, s))
  LogicNil' n -> Left (LogicNil' n)

data LogicNil'' c a = LogicNil''
data LogicCons'' n = LogicCons''

instance PrismA (LogicNil'' c a) (n, ()) (n', ()) where
  type Source (LogicNil'' c a) (n, ()) = LogicList' n c a
  make LogicNil'' = _LogicNil'

instance PrismA (LogicCons'' n) (c, (Term a, Term [a])) (c', (Term a', Term [a'])) where
  type Source (LogicCons'' n) (c, (Term a, Term [a])) = LogicList' n c a
  make LogicCons'' = _LogicCons'

instance (Logical a) => Matchable [a] (n, c) where
  type Matched [a] (n, c) = LogicList' n c a
  type Initial [a] = ((), ())

  enter LogicNil = LogicNil' ()
  enter (LogicCons a as) = LogicCons' () a as

  back (LogicNil' _) = LogicNil
  back (LogicCons' _ a as) = LogicCons a as

instance (Exhausted n, Exhausted c) => Exhausted (LogicList' n c a) where
  exhausted (LogicNil' n) = exhausted n
  exhausted (LogicCons' c _ _) = exhausted c

listo' :: forall a. (Logical a) => Term [a] -> Goal ()
listo' =
  matche'
    & on' LogicNil'' return
    & on' LogicCons'' (\(_ :: Term a, as :: Term [a]) -> listo' as)
    & enter'

eithers :: [Term (Either Bool Int)]
eithers = run eithero

lists' :: [Term [Int]]
lists' = run listo'

main :: IO ()
main = do
  putStrLn "lists:"
  mapM_ print (take 5 (showLogicList <$> lists))

  putStrLn "\npartitions [1, 2, 3]:"
  mapM_ print (partitions [1, 2, 3])

  putStrLn "\nnestedo:"
  mapM_ print (extract' <$> run nestedo)

  putStrLn "\nnestedo on Left:"
  mapM_ print (extract' <$> (run $ \x -> nestedo (Value (LogicLeft x))))

  putStrLn "\neithers:"
  mapM_ print (extract' <$> eithers)

  putStrLn "\nlists':"
  mapM_ print (take 5 (showLogicList <$> lists'))
