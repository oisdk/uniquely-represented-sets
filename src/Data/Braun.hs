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
fromList' = head . snd . rows
  where
    rows xs = foldr f (\_ _ -> (\_ _ -> [], [Leaf])) xs 1 1
    f e a !k m =
        case m of
            1 -> (\_ _ -> [], g e ys k zs (drop k zs)) where (ys,zs) = a (k * 2) k
            _ -> (g e ys m, zs) where (ys,zs) = a k (m - 1)
    g _ _ 0 _ _ = []
    g x xs !_ (y:ys) (z:zs) = Node x y z : xs ys zs
    g x xs !_ [] (z:zs) = Node x Leaf z : xs [] zs
    g x xs !_ (y:ys) [] = Node x y Leaf : xs ys []
    g x xs !_ [] [] = Node x Leaf Leaf : xs [] []
