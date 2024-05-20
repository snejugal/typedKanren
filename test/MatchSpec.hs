{-# LANGUAGE ScopedTypeVariables #-}

module MatchSpec (spec) where

import Data.Function ((&))
import Test.Hspec

import Core
import Goal
import LogicalBase
import Match

import Util

spec :: Spec
spec = do
  describe "non-exhaustive pattern matching" $ do
    let intToBoolo (n :: Term Int) =
          matche
            & on _False (\() -> n === Value 0)
            & on _True (\() -> n === Value 1)

    it "picks the correct arm when the value is known" $ do
      run (`intToBoolo` Value False) `shouldBe` [Value 0]
      run (`intToBoolo` Value True) `shouldBe` [Value 1]

    it "provides access to the fields" $ do
      let fooo =
            matche
              & on _LogicLeft (\n -> n === Value (42 :: Int))
              & on _LogicRight (\b -> b === Value True)

      run fooo
        `shouldSatisfy` isPermutationOf
          [ inject' (Left 42)
          , inject' (Right True)
          ]

    it "can generate values" $ do
      let solutions = run $ \b -> do
            n <- fresh
            intToBoolo n b
      solutions `shouldSatisfy` isPermutationOf [Value False, Value True]

    it "supports duplicated arms" $ do
      let duplicateso (n :: Term Int) =
            matche
              & on _False (\() -> n === Value 0)
              & on _False (\() -> n === Value (-1))
              & on _True (\() -> n === Value 1)

      run (`duplicateso` Value False)
        `shouldSatisfy` isPermutationOf [Value 0, Value (-1)]

    it "omitted arms lead to contradiction" $ do
      let isFalseo =
            matche
              & on _False return

      run (\() -> isFalseo (Value True)) `shouldBe` []

    it "supports nested patterns" $ do
      let intToMaybeBoolo (n :: Term Int) =
            matche
              & on (_LogicJust . _Value . _False) (\() -> n === Value 0)
              & on (_LogicJust . _Value . _True) (\() -> n === Value 1)
              & on _LogicNothing (\() -> n === Value 2)

      let allValues = run $ \b -> do
            n <- fresh
            intToMaybeBoolo n b
      allValues
        `shouldSatisfy` isPermutationOf
          [ inject' (Just False)
          , inject' (Just True)
          , inject' Nothing
          ]

      let insideJust = run $ \b -> do
            n <- fresh
            intToMaybeBoolo n (Value (LogicJust b))
      insideJust `shouldSatisfy` isPermutationOf [Value False, Value True]
