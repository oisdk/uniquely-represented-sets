{-# LANGUAGE DeriveFunctor #-}

module Main (main) where

import Criterion.Main
import Data.Braun

atSize :: Int -> Benchmark
atSize n =
    env (pure (fromList [1 .. n])) $
    \xs ->
         bgroup
             (show n)
             [ bench "uncons, just element" $ nf (fmap fst . uncons) xs
             , bench "uncons', just element" $ nf (fst . uncons') xs
             , bench "uncons, both" $ nf uncons xs
             , bench "uncons', both" $ nf uncons' xs ]


main =
    defaultMain
        [ atSize n
        | n <- [1000000, 3000000]]
