module Main (main) where

import Lib

main :: IO ()
main = do
    print (run (\x -> x === Known (42 :: Int)))
