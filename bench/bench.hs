{-# LANGUAGE DeriveFunctor #-}

module Main (main) where

import Criterion.Main
import Data.Braun

toListSize :: Int -> Benchmark
toListSize n =
    env (pure (fromList [1 .. n])) $
    \xs ->
         bgroup
             (show n)
             [ bench "trav" $ nf (flip runState (0 :: Int) . traverseBraun (\x -> State (\i -> (x,i+1)))) xs]

newtype State s a = State { runState :: s -> (a, s) } deriving Functor

instance Applicative (State s) where
    pure x = State (\s -> (x, s))
    fs <*> xs = State (\s -> case runState fs s of
                          (f,s') -> case runState xs s' of
                            (x,s'') -> (f x, s''))

main =
    defaultMain
        [ toListSize n
        | n <- [1000, 10000, 100000, 1000000, 3000000]]
