module Main (main) where

import Criterion.Main
import Data.Braun

toListSize :: Int -> Benchmark
toListSize n =
    env (pure (fromList [1 .. n])) $
    \xs ->
         bgroup
             (show n)
             [bench "old" $ nf toList' xs, bench "new" $ nf toList xs]

main =
    defaultMain
        [ toListSize (10 ^ n)
        | n <- [3 .. 8] ]
