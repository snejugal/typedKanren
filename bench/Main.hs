{-# LANGUAGE BangPatterns #-}

module Main (main) where

import Control.DeepSeq
import Criterion.Main
import Kanren.Core
import Kanren.Data.Binary (Binary)
import qualified Kanren.Data.Binary as Binary
import qualified Kanren.Data.Scheme as Scheme
import Kanren.Goal

exp3o :: Binary -> Term Binary -> Goal ()
exp3o n e3n = Binary.logo e3n (inject' 3) (inject' n) (inject' 0)

log3o :: Binary -> Term Binary -> Goal ()
log3o n log3n = do
  r <- fresh
  Binary.logo (inject' n) (inject' 3) log3n r

quineo :: () -> Term Scheme.SExpr -> Goal ()
quineo _ x = Scheme.evalo x (inject' []) (Value (Scheme.LogicSExpr x))

twineo :: () -> (Term Scheme.SExpr, Term Scheme.SExpr) -> Goal ()
twineo _ (x, y) = do
  Scheme.evalo x (inject' []) (Value (Scheme.LogicSExpr y))
  Scheme.evalo y (inject' []) (Value (Scheme.LogicSExpr x))

thrineo :: () -> (Term Scheme.SExpr, Term Scheme.SExpr, Term Scheme.SExpr) -> Goal ()
thrineo _ (x, y, z) = do
  Scheme.evalo x (inject' []) (Value (Scheme.LogicSExpr y))
  Scheme.evalo y (inject' []) (Value (Scheme.LogicSExpr z))
  Scheme.evalo z (inject' []) (Value (Scheme.LogicSExpr x))

whnfGoalOnce :: (Fresh v, NFData v) => (a -> v -> Goal ()) -> a -> Benchmarkable
whnfGoalOnce = whnfGoalN 1

whnfGoalN :: (Fresh v, NFData v) => Int -> (a -> v -> Goal ()) -> a -> Benchmarkable
whnfGoalN n f = nf $ \x -> take n (run (f x))

main :: IO ()
main =
  defaultMain
    [ bgroup
        "3^n "
        [ bench (" n=" <> show n) $ whnfGoalOnce exp3o (fromIntegral n)
        | n <- [0 .. 5 :: Int]
        ]
    , bgroup
        "log_3 n "
        [ bench (" n=" <> show n) $ whnfGoalOnce log3o (fromIntegral n)
        | p <- [0 .. 5 :: Int]
        , let n = 3 ^ p :: Int
        ]
    , bgroup
        "N quines "
        [ bench (" N=" <> show n) $ whnfGoalN n quineo ()
        | n <- [1, 100 :: Int]
        ]
    , bgroup
        "N twines "
        [ bench (" N=" <> show n) $ whnfGoalN n twineo ()
        | n <- [1, 15 :: Int]
        ]
    , bgroup
        "N thrines "
        [ bench (" N=" <> show n) $ whnfGoalN n thrineo ()
        | n <- [1, 2 :: Int]
        ]
    ]
