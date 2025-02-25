{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import Control.DeepSeq
import Criterion
import GHC.Stats
import Kanren.Core
import qualified Kanren.Data.Scheme as Scheme
import Kanren.Goal

twineo :: a -> (Term Scheme.SExpr, Term Scheme.SExpr) -> Goal ()
twineo a (x, y) = do
  _ <- return a
  Scheme.evalo x (inject' []) (Value (Scheme.LogicSExpr y))
  Scheme.evalo y (inject' []) (Value (Scheme.LogicSExpr x))

whnfGoalN :: (Fresh v, NFData v) => Int -> (a -> v -> Goal ()) -> a -> Benchmarkable
whnfGoalN n f = nf $ \x -> take n (run (f x))

main :: IO ()
main = do
  start <- getRTSStats
  benchmark (whnfGoalN 15 twineo ())
  end <- getRTSStats
  let peakAllocated = (max_mem_in_use_bytes end - max_mem_in_use_bytes start)
  putStrLn ("Peak allocated: " <> show peakAllocated <> " B")
