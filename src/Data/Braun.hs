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
fromList' = rows
  where
    rows xs = foldr f (\_ _ p -> p b [Leaf]) xs 1 1 (const head)

    f e a !k 1 p = a (k*2) k (\ys zs -> p b (g e ys zs (drop k zs)))
    f e a !k !m p = a k (m-1) (p . g e)

    b _ _ = []

    g x xs (y:ys) (z:zs) = Node x y    z    : xs ys zs
    g x xs [] (z:zs)     = Node x Leaf z    : xs [] zs
    g x xs (y:ys) []     = Node x y    Leaf : xs ys []
    g x xs [] []         = Node x Leaf Leaf : xs [] []
    {-# NOINLINE g #-}
