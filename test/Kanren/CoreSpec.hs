{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Kanren.CoreSpec (spec) where

import Data.Maybe (isNothing)
import Test.Hspec

import Kanren.Core
import Kanren.LogicalBase ()

is :: (Logical a, Eq (Logic a)) => Term a -> Term a -> Maybe State -> Bool
is _ _ Nothing = False
is var expected (Just state) = walk state var == expected

spec :: Spec
spec = do
  describe "unify'" $ do
    it "unifies variables and values" $ do
      let (state, x :: Term Int) = makeVariable empty

      unify' x (Value 42) state `shouldSatisfy` (x `is` Value 42)
      unify' (Value 37) x state `shouldSatisfy` (x `is` Value 37)

    it "handles transitivity" $ do
      let (stateA, x :: Term Int) = makeVariable empty
      let (stateB, y :: Term Int) = makeVariable stateA

      let stateC =
            unify' x y stateB
              >>= unify' y (Value 42)
      stateC `shouldSatisfy` (x `is` Value 42)

    it "detects contradictions" $ do
      let (stateA, x :: Term Int) = makeVariable empty
      let (stateB, y :: Term Int) = makeVariable stateA

      let stateC =
            unify' x (Value 42) stateB
              >>= unify' y (Value 37)
              >>= unify' x y
      stateC `shouldSatisfy` isNothing

    it "handles when a variable is unified with itself" $ do
      let (stateA, x :: Term Int) = makeVariable empty

      let stateB =
            unify' x x stateA
              >>= unify' x (Value 42)
      stateB `shouldSatisfy` (x `is` Value 42)
