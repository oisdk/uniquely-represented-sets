{-# LANGUAGE DeriveFunctor #-}

module Main (main) where

import Criterion.Main
import Data.Braun.Sized

atSize :: Int -> Benchmark
atSize n =
    env (pure (fromList [1 .. n])) $
    \xs ->
         bgroup
             (show n)
             [ bench "unsnoc, just element" $ nf (fmap fst . unsnoc) xs
             , bench "unsnoc', just element" $ nf (fst . unsnoc') xs
             , bench "unsnoc, both" $ nf unsnoc xs
             , bench "unsnoc', both" $ nf unsnoc' xs ]


main =
    defaultMain
        [ atSize n
        | n <- [1000000, 3000000]]
