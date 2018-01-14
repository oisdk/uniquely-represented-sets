module Data.Tree.Braun.Internal where

import Data.Tree.Binary (Tree(..))

-- | A specialised zip-like function which takes a continuation
-- rather than using explicit recursion.
zipLevels :: a
       -> ([Tree a] -> [Tree a] -> [Tree a])
       -> [Tree a]
       -> [Tree a]
       -> [Tree a]
zipLevels x a (y:ys) (z:zs) = Node x y    z    : a ys zs
zipLevels x a [] (z:zs)     = Node x Leaf z    : a [] zs
zipLevels x a (y:ys) []     = Node x y    Leaf : a ys []
zipLevels x a [] []         = Node x Leaf Leaf : a [] []
{-# NOINLINE zipLevels #-}
