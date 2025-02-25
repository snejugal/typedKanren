{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import Control.DeepSeq
import Criterion
import GHC.Stats
import Kanren.Core
import Kanren.Data.Binary (Binary)
import qualified Kanren.Data.Binary as Binary
import Kanren.Goal

exp3o :: Binary -> Term Binary -> Goal ()
exp3o n e3n = Binary.logo e3n (inject' 3) (inject' n) (inject' 0)

whnfGoalOnce :: (Fresh v, NFData v) => (a -> v -> Goal ()) -> a -> Benchmarkable
whnfGoalOnce = whnfGoalN 1

whnfGoalN :: (Fresh v, NFData v) => Int -> (a -> v -> Goal ()) -> a -> Benchmarkable
whnfGoalN n f = nf $ \x -> take n (run (f x))

main :: IO ()
main = do
  start <- getRTSStats
  benchmark (whnfGoalOnce exp3o (fromIntegral 5))
  end <- getRTSStats
  let peakAllocated = (max_mem_in_use_bytes end - max_mem_in_use_bytes start)
  putStrLn ("Peak allocated: " <> show peakAllocated <> " B")
