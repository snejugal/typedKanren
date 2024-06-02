{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Kanren.CoreSpec (spec) where

import Data.Maybe (isJust, isNothing)
import Test.Hspec

import Kanren.Core
import Kanren.LogicalBase ()

is :: (Logical a, Eq (Logic a)) => Term a -> Term a -> Maybe State -> Bool
is _ _ Nothing = False
is var expected (Just state) = walk' state var == expected

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

  describe "disequality" $ do
    it "succeeds when two terms are not equal" $ do
      disequality (Value True) (Value False) empty `shouldSatisfy` isJust

    it "fails when two terms are equal" $ do
      disequality (Value True) (Value True) empty `shouldSatisfy` isNothing

    it "keeps track of constraints on variables" $ do
      let (stateA, x :: Term Bool) = makeVariable empty
      let stateB = disequality x (Value True) stateA

      (unify' x (Value False) =<< stateB) `shouldSatisfy` (x `is` Value False)
      (unify' x (Value True) =<< stateB) `shouldSatisfy` isNothing

    it "works when constraining two complex structures" $ do
      let (stateA, x :: Term Bool) = makeVariable empty
      let (stateB, y :: Term Int) = makeVariable stateA
      let stateC = disequality (Value (x, y)) (Value (Value True, Value 42)) stateB

      (unify' x (Value True) =<< stateC) `shouldSatisfy` (x `is` Value True)
      (unify' y (Value 42) =<< stateC) `shouldSatisfy` (y `is` Value 42)

      let stateD = unify' x (Value True) =<< stateC
      (unify' y (Value 42) =<< stateD) `shouldSatisfy` isNothing
      (unify' y (Value 37) =<< stateD) `shouldSatisfy` (y `is` Value 37)

      let stateD' = unify' y (Value 42) =<< stateC
      (unify' x (Value True) =<< stateD') `shouldSatisfy` isNothing
      (unify' x (Value False) =<< stateD') `shouldSatisfy` (x `is` Value False)

    it "works when constraining a variable and a complex structure" $ do
      let (stateA, x :: Term (Bool, Int)) = makeVariable empty
      let (stateB, y :: Term Int) = makeVariable stateA
      let stateC = disequality x (Value (Value True, Value 42)) stateB

      let stateD = unify' x (Value (Value True, y)) =<< stateC
      stateD `shouldSatisfy` isJust
      (unify' y (Value 42) =<< stateD) `shouldSatisfy` isNothing

    it "works when constraining two variables" $ do
      let (stateA, x :: Term Bool) = makeVariable empty
      let (stateB, y :: Term Bool) = makeVariable stateA
      let (stateC, z :: Term Bool) = makeVariable stateB

      let stateD = disequality x y stateC
      (unify' x z =<< stateD) `shouldSatisfy` isJust
      (unify' y z =<< stateD) `shouldSatisfy` isJust
      (unify' x y =<< stateD) `shouldSatisfy` isNothing

    it "works transitively" $ do
      let (stateA, x :: Term Bool) = makeVariable empty
      let (stateB, y :: Term Bool) = makeVariable stateA

      let stateC =
            disequality x (Value True) stateB
              >>= unify' x y

      (unify' y (Value False) =<< stateC) `shouldSatisfy` (x `is` Value False)
      (unify' y (Value True) =<< stateC) `shouldSatisfy` isNothing

      let stateC' =
            disequality x (Value True) stateB
              >>= unify' y x

      (unify' y (Value False) =<< stateC') `shouldSatisfy` (x `is` Value False)
      (unify' y (Value True) =<< stateC') `shouldSatisfy` isNothing
