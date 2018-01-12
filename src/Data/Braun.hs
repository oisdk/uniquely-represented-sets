{-# LANGUAGE BangPatterns #-}

module Data.Braun where

-- import qualified Data.Tree as Tree
import Data.Tree (Tree(..))
import GHC.Base (build)

preFromList :: [a] -> Tree a
preFromList [] = Leaf
preFromList (x:xs) =
    let (od,ev) = unLink $ preFromList $ pairUp xs
    in Node x od ev

pairUp :: [a] -> [(a, Maybe a)]
pairUp [] = []
pairUp [x] = [(x,Nothing)]
pairUp (x:y:ys) = (x,Just y):pairUp ys

unLink :: Tree (a,Maybe b) -> (Tree a,Tree b)
unLink Leaf = (Leaf,Leaf)
unLink (Node (x,Nothing) Leaf Leaf) = (Node x Leaf Leaf,Leaf)
unLink (Node (x,Just y) od ev) =
  let (odx,ody) = unLink od
      (evx,evy) = unLink ev
  in (Node x odx evx, Node y ody evy)

toList :: Tree a -> [a]
toList Leaf = []
toList (Node x ys zs) = x:go [ys,zs] [] []
  where go [] [] [] = []
        go [] r s = go (reverse r ++ reverse s) [] []
        go (Leaf:ps) l r = go ps l r
        go (Node p qs rs:ss) l r = p:go ss (qs:l) (rs:r)

-- |
--
-- prop> fromList' xs == preFromList (xs :: [Int])
fromList' :: [a] -> Tree a
fromList' = head . rows where
  make k xs ts = zipWith3 Node xs ts1 ts2 where
    (ts1,ts2) = splitAt k (ts ++ repeat Leaf)
  rows xs = snd (foldr f b xs 1 1) where
    f e a !k 1 = let (ys,zs) = a (k*2) k in ([], make k (e:ys) zs)
    f e a !k m = let (ys,zs) = a k (m-1) in (e:ys,zs)
    b _ _ = ([],[Leaf])

-- z3n k xs ts =
