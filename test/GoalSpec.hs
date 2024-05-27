{-# LANGUAGE ScopedTypeVariables #-}

module GoalSpec (spec) where

import Test.Hspec

import Core
import Goal
import LogicalBase ()

import Util

spec :: Spec
spec = do
  it "failo fails" $
    run (\() -> failo) `shouldBe` []

  it "(===) unifies values" $ do
    run (\x -> x === Value '5') `shouldBe` [Value '5']

  describe "conj" $ do
    it "performs conjunction" $ do
      let solutions = run $ \(x, y) ->
            (x === Value True) `conj` (y === Value 'c')
      solutions `shouldBe` [(Value True, Value 'c')]

    it "handles contradictions" $ do
      let solutions = run $ \x ->
            (x === Value True) `conj` (x === Value False)
      solutions `shouldBe` []

  it "conjMany performs conjunction of several goals" $ do
    let solutions = run $ \(x, y :: Term Int, z) ->
          conjMany
            [ x === Value 'a'
            , y === Value 42
            , z === Value True
            ]
    solutions `shouldBe` [(Value 'a', Value 42, Value True)]

  it "disj performs disjunction" $ do
    let solutions = run $ \x ->
          (x === Value True) `disj` (x === Value False)
    solutions `shouldSatisfy` isPermutationOf [Value True, Value False]

  it "disjMany performs disjunction of several goals" $ do
    let solutions = run $ \x ->
          disjMany
            [ x === Value '1'
            , x === Value '2'
            , x === Value '3'
            ]
    solutions `shouldSatisfy` isPermutationOf [Value '1', Value '2', Value '3']

  it "conde works correctly" $ do
    let solutions = run $ \(x, y) ->
          conde
            [ [x === Value True, y === Value '(']
            , [x === Value False, y === Value ')']
            ]
    solutions
      `shouldSatisfy` isPermutationOf
        [ (Value True, Value '(')
        , (Value False, Value ')')
        ]

  it "fresh creates new variables each time" $ do
    let solutions = run $ \() -> do
          a <- fresh
          b <- fresh
          a === Value True
          b === Value False

    solutions `shouldBe` [()]
