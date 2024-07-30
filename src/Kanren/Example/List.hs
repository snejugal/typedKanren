{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Kanren.Example.List (example) where

import Control.Monad.ST (runST)
import Data.Function ((&))
import Data.Maybe (fromJust)

import Kanren.Core
import Kanren.Goal
import Kanren.LogicalBase
import Kanren.Match

listo :: (Logical a) => Term s [a] -> Goal s ()
listo =
  matche
    & on _LogicNil return
    & on _LogicCons (\(_, xs) -> listo xs)

{- FOURMOLU_DISABLE -}
appendo :: (Logical a) => Term s [a] -> Term s [a] -> Term s [a] -> Goal s ()
appendo xs ys zs = xs & (matche
  & on _LogicNil (\() -> ys === zs)
  & on _LogicCons (\(x, xs') -> do
      zs' <- fresh
      zs === Value (LogicCons x zs')
      appendo xs' ys zs'))
{- FOURMOLU_ENABLE -}

partitions :: (Logical a) => [a] -> [([a], [a])]
partitions xs = runST (fmap reifyBoth <$> partitioned)
 where
  partitioned = run' $ \(left, right) -> do
    appendo left right (inject' xs)

  reifyBoth (a, b) = (reify a, reify b)
  reify = fromJust . extract'

example :: IO ()
example = do
  putStrLn "listo:"
  mapM_ putStrLn (runST (map show <$> run 5 (listo @Int)))

  putStrLn "\npartitions [1, 2, 3]:"
  mapM_ print $ partitions [1 :: Int, 2, 3]
