-- | This module provides functions to test Braun trees for invariants
-- and properties.
module Data.Tree.Braun.Sized.Properties where

import qualified Data.Tree.Braun.Properties as Unsized
import           Data.Tree.Braun.Sized

import           Data.Foldable
import           Data.List                  (sortBy)
import           Data.Functor.Classes

-- | Returns True iff the stored size in the Braun tree is its actual
-- size.
validSize :: Braun a -> Bool
validSize (Braun n xs) = n == length xs

-- | Returns True iff the tree is a proper Braun tree.
isBraun :: Braun a -> Bool
isBraun (Braun _ xs) = Unsized.isBraun xs

-- | Returns True iff the elements of the tree are in order.
inOrder :: (a -> a -> Ordering) -> Braun a -> Bool
inOrder cmp b = liftCompare cmp (sortBy cmp xs) xs == EQ where
  xs = toList b
