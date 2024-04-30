{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Data.Function ((&))

import Core
import Goal
import Match
import UnifiableBase

listo :: Unifiable a => ValueOrVar [a] -> Goal ()
listo = matche
  & on _LogicNil return
  & on _LogicCons (\(_, xs) -> listo xs)

showLogicList :: Show (Term a) => ValueOrVar [a] -> String
showLogicList xs = prefix ++ go xs ++ suffix
  where
    (prefix, suffix) = case xs of
      Value _ -> ("[", "]")
      _ -> ("", "")

    go (Var _) = "..?"
    go (Value LogicNil) = ""
    go (Value (LogicCons x xs)) = show x ++ sep ++ go xs
      where
        sep = case xs of
          Value LogicNil -> ""
          _ -> ", "

main :: IO ()
main = mapM_ print (take 5 (showLogicList <$> run (listo @Int)))
