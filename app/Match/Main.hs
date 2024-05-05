{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Function ((&))
import Data.Maybe (fromJust)
import Data.Void (Void)
import Control.Lens (Iso, iso)

import Core
import Goal
import Match
import UnifiableBase

listo :: Unifiable a => ValueOrVar [a] -> Goal ()
listo = matche
  & on _LogicNil return
  & on _LogicCons (\(_, xs) -> listo xs)

appendo :: Unifiable a => ValueOrVar [a] -> ValueOrVar [a] -> ValueOrVar [a] -> Goal ()
appendo xs ys zs = xs & (matche
  & on _LogicNil (\() -> ys === zs)
  & on _LogicCons (\(x, xs') ->
      fresh $ \zs' -> do
        zs === Value (LogicCons x zs')
        appendo xs' ys zs'))

showLogicList :: Show (Term a) => ValueOrVar [a] -> String
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

lists :: [ValueOrVar [Int]]
lists = run listo

partitions :: [Int] -> [([Int], [Int])]
partitions xs = fmap (fromJust . extract') $ run $
  \result -> fresh $ \(left, right) -> do
    result === Value (left, right)
    appendo left right (inject' xs)

-- Exhaustive pattern-matching

_LogicLeft' :: Biprism (LogicEither a c) (LogicEither b c) (ValueOrVar a) (ValueOrVar b)
_LogicLeft' = biprism LogicLeft LogicLeft $ \case
  LogicLeft a -> Right a
  LogicRight b -> Left (LogicRight b)

_LogicRight' :: Biprism (LogicEither c a) (LogicEither c b) (ValueOrVar a) (ValueOrVar b)
_LogicRight' = biprism LogicRight LogicRight $ \case
  LogicRight a -> Right a
  LogicLeft b -> Left (LogicLeft b)

eithero :: ValueOrVar (Either Bool Int) -> Goal ()
eithero = matche'
  & on' _LogicLeft' (\x -> x === Value True)
  & on' _LogicRight' (\x -> x === Value 42)

eithers :: [ValueOrVar (Either Bool Int)]
eithers = run eithero

main :: IO ()
main = do
  putStrLn "lists:"
  mapM_ print (take 5 (showLogicList <$> lists))

  putStrLn "\npartitions [1, 2, 3]:"
  mapM_ print (partitions [1, 2, 3])

  putStrLn "\neithers:"
  mapM_ print (extract' <$> eithers)
