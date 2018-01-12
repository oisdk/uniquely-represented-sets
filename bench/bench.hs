module Main (main) where

import Criterion.Main
import Data.Braun

main = defaultMain
   [ bench "1" $ nf preFromList [(1 :: Int)..10000]
   , bench "2" $ nf fromList'   [(1 :: Int)..10000]]
