{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Data.Function ((&))
import Data.Maybe (fromJust)

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

main :: IO ()
main = do
  putStrLn "lists:"
  mapM_ print (take 5 (showLogicList <$> lists))

  putStrLn "\npartitions [1, 2, 3]:"
  mapM_ print (partitions [1, 2, 3])
