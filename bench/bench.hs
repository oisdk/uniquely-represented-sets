module Main (main) where

import           Control.Monad (replicateM)
import           Criterion.Main
import           Data.Foldable
import           Data.Set.Unique
import           System.Random

insert'
    :: Ord a
    => a -> [a] -> [a]
insert' x (y:ys)
  | x > y = y : insert' x ys
insert' x ys = x : ys

member' :: Ord a => a -> [a] -> Bool
member' x = foldr f False where
  f y ys = case compare x y of
    LT -> False
    GT -> ys
    EQ -> True

intr :: Int -> IO Int
intr u = randomRIO (0,u)

atSize :: Int -> Benchmark
atSize n =
    env
        ((,,) <$> replicateM n (intr n) <*>
         fmap fromList (replicateM n (intr n)) <*> fmap (foldr insert' []) (replicateM n (intr n))) $
    \ ~(xs,ys,zs) ->
         bgroup
             (show n)
             [ bench "member" $ nf (length . filter (`member` ys)) xs
             , bench "listMember" $ nf (length . filter (`member'` zs)) xs
             , bench "insert" $ nf (foldl' (flip insert) empty) xs
             , bench "listInsert" $ nf (foldl' (flip insert') []) xs
             , bench "fromList" $ nf fromList xs
             , bench "fromListBy" $ nf (fromListBy compare) xs]


main :: IO ()
main = defaultMain (map atSize [1000, 10000])
