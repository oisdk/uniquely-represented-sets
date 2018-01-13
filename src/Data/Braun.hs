{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes          #-}

module Data.Braun where

-- import qualified Data.Tree as Tree
import           Data.Tree (Tree (..))
import           GHC.Base  (build)

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
toList t = build (\(c :: a -> b -> b) (n :: b) ->
  let b :: [Tree a] -> [Tree a] -> b
      b [] _ = n
      b _ [] = n
      b r s  = foldr revf id r (foldr revf id s b) [] []
      go :: Tree a -> ([Tree a] -> [Tree a] -> b) -> [Tree a] -> [Tree a] -> b
      go Leaf ps l r           = ps l r
      go (Node p qs rs) ss l r = p `c` ss (qs:l) (rs:r)
      revf x y z  = y (go x z)
  in go t b [] [])

-- |
--
-- prop> toList (fromList xs) == (xs :: [Int])
fromList :: [a] -> Tree a
fromList xs = foldr f (\_ _ p -> p b [Leaf]) xs 1 1 (const head)
  where
    f e a !k 1 p  = a (k*2) k (\ys zs -> p b (g e ys zs (drop k zs)))
    f e a !k !m p = a k (m-1) (p . g e)

    b _ _ = []

    g x a (y:ys) (z:zs) = Node x y    z    : a ys zs
    g x a [] (z:zs)     = Node x Leaf z    : a [] zs
    g x a (y:ys) []     = Node x y    Leaf : a ys []
    g x a [] []         = Node x Leaf Leaf : a [] []
    {-# NOINLINE g #-}

toList' Leaf = []
toList' t = tol [t]
  where tol [] = []
        tol ts = xs ++ tol (ts1 ++ ts2)
          where xs = map root ts
                (ts1,ts2) = children ts

                children [] = ([],[])
                children (Node _ Leaf _ : _) = ([],[])
                children (Node _ a Leaf : ts) = (a : leftChildren ts, [])
                children (Node _ a b : ts) = (a : ts1, b : ts2)
                  where (ts1, ts2) = children ts
                children _ = error "BraunSeq.toList: bug!"

                leftChildren [] = []
                leftChildren (Node _ Leaf _ : _) = []
                leftChildren (Node _ a _ : ts) = a : leftChildren ts
                leftChildren _ = error "BraunSeq.toList: bug!"

                root (Node x _ _) = x
                root _            = error "BraunSeq.toList: bug!"

                (Node _ a _) = a
