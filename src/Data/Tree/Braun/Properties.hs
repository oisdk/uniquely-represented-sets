module Data.Tree.Braun.Properties where

import Data.Tree.Binary

-- | Returns true iff the tree is a Braun tree.
isBraun :: Tree a -> Bool
isBraun = zygoTree (0 :: Int) (\_ l r -> 1 + l + r) True alg
  where
    alg _ lsize lbrn rsize rbrn =
        lbrn && rbrn && (lsize == rsize || lsize - 1 == rsize)
