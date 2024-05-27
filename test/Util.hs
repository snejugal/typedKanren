module Util (isPermutationOf) where

isPermutationOf :: (Eq a) => [a] -> [a] -> Bool
isPermutationOf xs ys =
  length xs == length ys
    && all (`elem` ys) xs
    && all (`elem` xs) ys
