{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Kanren.Example.List (example) where

import Data.Function ((&))
import Data.Maybe (fromJust)

import Kanren.Core
import Kanren.Goal
import Kanren.LogicalBase
import Kanren.Match

listo :: (Logical a) => Term [a] -> Goal ()
listo =
  matche
    & on _LogicNil return
    & on _LogicCons (\(_, xs) -> listo xs)

{- FOURMOLU_DISABLE -}
appendo :: (Logical a) => Term [a] -> Term [a] -> Term [a] -> Goal ()
appendo xs ys zs = xs & (matche
  & on _LogicNil (\() -> ys === zs)
  & on _LogicCons (\(x, xs') -> do
      zs' <- fresh
      zs === Value (LogicCons x zs')
      appendo xs' ys zs'))
{- FOURMOLU_ENABLE -}

partitions :: (Logical a) => [a] -> [([a], [a])]
partitions xs = reifyBoth <$> partitioned
 where
  partitioned = run $ \(left, right) -> do
    appendo left right (inject' xs)

  reifyBoth (a, b) = (reify a, reify b)
  reify = fromJust . extract'

example :: IO ()
example = do
  putStrLn "listo:"
  mapM_ print $ take 5 (run (listo @Int))

  putStrLn "\npartitions [1, 2, 3]:"
  mapM_ print $ partitions [1 :: Int, 2, 3]
