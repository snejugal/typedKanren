{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLists #-}

module Main (main) where

import Core
import Goal
import UnifiableBase

pattern LogicNil' :: Unifiable a => (forall x. Goal x -> CaseGoal x) -> Matched [a]
pattern LogicNil' applyEffects <- (matchLogicNil -> Just applyEffects)

matchLogicNil :: Unifiable a => Matched [a] -> Maybe (forall x. Goal x -> CaseGoal x)
matchLogicNil (Matched (_, Value LogicNil)) = Just CaseGoal
matchLogicNil (Matched (_, Value _)) = Nothing
matchLogicNil (Matched (state, Var t)) = Just applyEffects
  where
    state' = state
    applyEffects :: forall x. Goal x -> CaseGoal x
    applyEffects g = CaseGoal (Goal (\_ -> runGoal (Var t === Value LogicNil >> g) state'))

pattern LogicCons' :: Unifiable a => (forall x. Goal x -> CaseGoal x) -> ValueOrVar a -> ValueOrVar [a] -> Matched [a]
pattern LogicCons' applyEffects x xs <- (matchLogicCons -> Just (applyEffects, x, xs))

matchLogicCons :: Unifiable a => Matched [a] -> Maybe (forall x. Goal x -> CaseGoal x, ValueOrVar a, ValueOrVar [a])
matchLogicCons (Matched (_, Value (LogicCons x xs))) = Just (CaseGoal, x, xs)
matchLogicCons (Matched (_, Value _)) = Nothing
matchLogicCons (Matched (state, Var t)) = Just (applyEffects, x, xs)
  where
    (state', x) = makeVariable state
    (state'', xs) = makeVariable state'
    applyEffects :: Goal x -> CaseGoal x
    applyEffects g = CaseGoal (Goal (\_ -> runGoal (Var t === Value (LogicCons x xs) >> g) state''))

foo :: ValueOrVar [Int] -> Goal ()
foo x = mcase x $ \case
  LogicCons' applyEffects x xs -> applyEffects $ do
    x === 0
    xs === []
  LogicNil' applyEffects -> applyEffects $ return ()

main :: IO ()
main = print $ extract' <$> run foo
