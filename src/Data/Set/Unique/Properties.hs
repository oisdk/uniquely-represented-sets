-- | This module provides functions for testing invariants and
-- properties on the uniquely-represented sets.
module Data.Set.Unique.Properties where

import           Data.Set.Unique
import qualified Data.Tree.Braun.Sized as Braun
import qualified Data.Tree.Braun.Sized.Properties as Braun

import           Data.Foldable

import           Data.List (sortBy)
import           Data.Functor.Classes

-- | Check that the sizes of the inner Braun trees obey the size
-- bound.
sizesInBound :: Set a -> Bool
sizesInBound (Set b) = null xs || it && re where
  xs = toList b
  it = and $ zipWith (\x y -> Braun.size x == szfn y) (safeInit xs) [1..]
  safeInit [] = []
  safeInit ys = init ys
  re = Braun.size (last xs) <= szfn (length xs)

-- | Check that all inner trees are Braun trees.
allBraun :: Set a -> Bool
allBraun (Set b) = Braun.isBraun b && all Braun.isBraun b

-- | Check that the elements are stored in the correct order.
inOrder :: (a -> a -> Ordering) -> Set a -> Bool
inOrder cmp xs =
    liftEq
        (\x y ->
              cmp x y == EQ)
        ys
        (sortBy cmp ys)
  where
    ys = toList xs

-- | Check that all inner trees store the correct size.
allCorrectSizes :: Set a -> Bool
allCorrectSizes (Set b) = Braun.validSize b && all Braun.validSize b

-- | Check that the stored size is correct.
validSize :: Set a -> Bool
validSize s = length s == foldl' (\a _ -> a + 1) 0 s
