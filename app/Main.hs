{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Lib

main :: IO ()
main = do
    print (run (\(x :: ValueOrVar Int) -> x === 42))
