{-# LANGUAGE BangPatterns #-}

module Data.Braun where

-- import qualified Data.Tree as Tree
import Data.Tree (Tree(..))
import GHC.Base (build)

-- preFromList :: [a] -> Tree a
-- preFromList [] = Leaf
-- preFromList (x:xs) =
--     let (od,ev) = unLink $ preFromList $ pairUp xs
--     in Node x od ev

-- pairUp :: [a] -> [(a, Maybe a)]
-- pairUp [] = []
-- pairUp [x] = [(x,Nothing)]
-- pairUp (x:y:ys) = (x,Just y):pairUp ys

-- unLink :: Tree (a,Maybe b) -> (Tree a,Tree b)
-- unLink Leaf = (Leaf,Leaf)
-- unLink (Node (x,Nothing) Leaf Leaf) = (Node x Leaf Leaf,Leaf)
-- unLink (Node (x,Just y) od ev) =
--   let (odx,ody) = unLink od
--       (evx,evy) = unLink ev
--   in (Node x odx evx, Node y ody evy)

toList :: Tree a -> [a]
toList t = build (\c n ->
  let b _ [] = n
      b r s = revf go r (revf go s b) [] []
      go Leaf ps l r = ps l r
      go (Node p qs rs) ss l r = p `c` ss (qs:l) (rs:r)
      revf f = foldr (flip (.) . f) id
  in go t b [] [])

-- |
--
-- prop> toList (fromList xs) == (xs :: [Int])
fromList :: [a] -> Tree a
fromList xs = foldr f (\_ _ p -> p b [Leaf]) xs 1 1 (const head)
  where
    f e a !k 1 p = a (k*2) k (\ys zs -> p b (g e ys zs (drop k zs)))
    f e a !k !m p = a k (m-1) (p . g e)

    b _ _ = []

    g x a (y:ys) (z:zs) = Node x y    z    : a ys zs
    g x a [] (z:zs)     = Node x Leaf z    : a [] zs
    g x a (y:ys) []     = Node x y    Leaf : a ys []
    g x a [] []         = Node x Leaf Leaf : a [] []
    {-# NOINLINE g #-}
