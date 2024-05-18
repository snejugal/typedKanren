{-# LANGUAGE TemplateHaskell #-}

module GoalTests (runTests) where

import Test.QuickCheck.All (quickCheckAll)

import Core
import Goal
import LogicalBase ()

permutationOf :: (Eq a) => [a] -> [a] -> Bool
permutationOf xs ys = length xs == length ys && all (`elem` ys) xs && all (`elem` xs) ys

prop_failo :: Bool
prop_failo = null (run (\() -> failo))

prop_success :: Bool
prop_success = run return == [()]

prop_unify :: Int -> Bool
prop_unify x = run (\var -> var === Value x) == [Value x]

prop_disj :: Int -> Int -> Bool
prop_disj x y =
  permutationOf
    [Value x, Value y]
    (run (\var -> (var === Value x) `disj` (var === Value y)))

prop_conj :: Int -> Int -> Bool
prop_conj x y =
  run (\var -> (var === Value x) `conj` (var === Value y))
    == expected
 where
  expected
    | x == y = [Value x]
    | otherwise = []

prop_fresh :: Bool
prop_fresh = case result of
  [Value (Var x, Var xs)] -> x /= xs
  _ -> False
 where
  result :: [Term (Bool, Bool)]
  result = run $ \var -> do
    x <- fresh
    xs <- fresh
    var === Value (x, xs)

prop_conjMany :: Int -> Int -> Int -> Bool
prop_conjMany x y z =
  [(Value x, Value y, Value z)]
    == run
      ( \(a, b, c) ->
          conjMany
            [ a === Value x
            , b === Value y
            , c === Value z
            ]
      )

prop_disjMany :: [Int] -> Bool
prop_disjMany xs =
  permutationOf
    (map Value xs)
    ( run $
        \var ->
          disjMany (map (\x -> var === Value x) xs)
    )

prop_conde :: Bool -> Bool -> Int -> Int -> Bool
prop_conde s t x y =
  [(Value s, Value x), (Value t, Value y)]
    == run
      ( \(a, b) ->
          conde
            [ [a === Value s, b === Value x]
            , [a === Value t, b === Value y]
            ]
      )

return []
runTests :: IO Bool
runTests = $quickCheckAll
