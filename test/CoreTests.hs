{-# LANGUAGE TemplateHaskell #-}

module CoreTests (runTests) where

import Data.Maybe (isJust)
import Test.QuickCheck.All (quickCheckAll)

import Core
import LogicalBase ()

prop_unification :: Int -> Bool -> Bool
prop_unification a onLeft = case state' of
  Nothing -> False
  Just state'' -> walk state'' x == Value a
 where
  x :: Term Int
  (state, x) = makeVariable empty
  state'
    | onLeft = unify' x (Value a) state
    | otherwise = unify' (Value a) x state

prop_unificationTransitivity :: Int -> Bool
prop_unificationTransitivity a = case state' of
  Nothing -> False
  Just state'' -> walk state'' x == Value a
 where
  x, y :: Term Int
  (stateX, x) = makeVariable empty
  (stateY, y) = makeVariable stateX
  state' = do
    stateA <- unify' x y stateY
    unify' y (Value a) stateA

prop_unificationContradiction :: Int -> Int -> Bool
prop_unificationContradiction a b = (a == b) == isJust state'
 where
  x, y :: Term Int
  (stateX, x) = makeVariable empty
  (stateY, y) = makeVariable stateX
  state' = do
    stateA <- unify' x (Value a) stateY
    stateB <- unify' x (Value b) stateA
    unify' x y stateB

prop_unificationSameVariable :: Int -> Bool
prop_unificationSameVariable a = case state' of
  Nothing -> False
  Just state'' -> walk state'' x == Value a
 where
  x :: Term Int
  (state, x) = makeVariable empty
  state' = do
    stateA <- unify' x x state
    unify' x (Value a) stateA

return []
runTests :: IO Bool
runTests = $quickCheckAll
