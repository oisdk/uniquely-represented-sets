{-# LANGUAGE BangPatterns        #-}

-- | This module provides functions for manipulating and using Braun
-- trees.
module Data.Tree.Braun
  (
   -- * Construction
   fromList
  ,replicate
  ,singleton
  ,empty
   -- ** Building
  ,Builder
  ,consB
  ,nilB
  ,runB
  ,
   -- * Modification
   cons
  ,uncons
  ,uncons'
  ,tail
  ,
   -- * Consuming
   foldrBraun
  ,toList
  ,
   -- * Querying
   (!)
  ,(!?)
  ,size
  ,UpperBound(..)
  ,ub)
  where

import           Data.Tree.Binary (Tree (..))
import qualified Data.Tree.Binary as Binary
import           GHC.Base  (build)
import           Prelude hiding (tail, replicate)
import           Data.Tree.Braun.Internal (zipLevels)
import           GHC.Stack

-- | A Braun tree with one element.
singleton :: a -> Tree a
singleton = Binary.singleton
{-# INLINE singleton #-}

-- | A Braun tree with no elements.
empty :: Tree a
empty = Leaf
{-# INLINE empty #-}

-- | /O(n)/. Create a Braun tree (in order) from a list. The algorithm
-- is similar to that in:
--
-- Okasaki, Chris. ‘Three Algorithms on Braun Trees’. Journal of
-- Functional Programming 7, no. 6 (November 1997): 661–666.
-- https://doi.org/10.1017/S0956796897002876.
--
-- However, it uses a fold rather than explicit recursion, allowing
-- fusion.
--
-- Inlined sufficiently, the implementation is:
--
-- @
-- fromList :: [a] -> 'Tree' a
-- fromList xs = 'foldr' f b xs 1 1 ('const' 'head') where
--   f e a !k 1  p = a (k'*'2) k     (\ys zs -> p n (g e ys zs ('drop' k zs)))
--   f e a !k !m p = a k     (m'-'1) (p . g e)
--
--   g x a (y:ys) (z:zs) = 'Node' x y    z    : a ys zs
--   g x a []     (z:zs) = 'Node' x 'Leaf' z    : a [] zs
--   g x a (y:ys) []     = 'Node' x y    'Leaf' : a ys []
--   g x a []     []     = 'Node' x 'Leaf' 'Leaf' : a [] []
--   {-\# NOINLINE g #-}
--
--   n _ _ = []
--   b _ _ p = p n [Leaf]
-- {-\# INLINABLE fromList #-}
-- @
--
-- prop> toList (fromList xs) == xs
fromList :: [a] -> Tree a
fromList xs = runB (foldr consB nilB xs)
{-# INLINABLE fromList #-}

-- | A type suitable for building a Braun tree by repeated applications
-- of 'consB'.
type Builder a b = (Int -> Int -> (([Tree a] -> [Tree a] -> [Tree a]) -> [Tree a] -> b) -> b)

-- | /O(1)/. Push an element to the front of a 'Builder'.
consB :: a -> Builder a b -> Builder a b
consB e a !k 1 p  = a (k*2) k (\ys zs -> p (\_ _ -> []) (zipLevels e ys zs (drop k zs)))
consB e a !k !m p = a k (m-1) (p . zipLevels e)
{-# INLINE consB #-}

-- | An empty 'Builder'.
nilB :: Builder a b
nilB _ _ p = p (\_ _ -> []) [Leaf]
{-# INLINE nilB #-}

-- | Convert a 'Builder' to a Braun tree.
runB :: Builder a (Tree a) -> Tree a
runB b = b 1 1 (const head)
{-# INLINE runB #-}


-- | Perform a right fold, in Braun order, over a tree.
foldrBraun :: Tree a -> (a -> b -> b) -> b -> b
foldrBraun tr c n =
    case tr of
        Leaf -> n
        _ -> tol [tr]
            where tol [] = n
                  tol xs = foldr (c . root) (tol (children xs id)) xs
                  children [] k = k []
                  children (Node _ Leaf _:_) k = k []
                  children (Node _ l Leaf:ts) k =
                      l : foldr leftChildren (k []) ts
                  children (Node _ l r:ts) k = l : children ts (k . (:) r)
                  children _ _ =
                      errorWithoutStackTrace "Data.Tree.Braun.toList: bug!"
                  leftChildren (Node _ Leaf _) _ = []
                  leftChildren (Node _ l _) a = l : a
                  leftChildren _ _ =
                      errorWithoutStackTrace "Data.Tree.Braun.toList: bug!"
                  root (Node x _ _) = x
                  root _ = errorWithoutStackTrace "Data.Tree.Braun.toList: bug!"
{-# INLINE foldrBraun #-}

-- | /O(n)/. Convert a Braun tree to a list.
--
-- prop> fromList (toList xs) === xs
toList :: Tree a -> [a]
toList tr = build (foldrBraun tr)
{-# INLINABLE toList #-}

-- | /O(log^2 n)/. Calculate the size of a Braun tree.
size :: Tree a -> Int
size Leaf = 0
size (Node _ l r) = 1 + 2 * m + diff l m where
  m = size r
  diff Leaf 0 = 0
  diff (Node _ Leaf Leaf) 0 = 1
  diff (Node _ s t) k
      | odd k = diff s (k `div` 2)
      | otherwise = diff t ((k `div` 2) - 1)
  diff Leaf _ = errorWithoutStackTrace "Data.Tree.Braun.size: bug!"

-- | /O(log^2 n)/. @'replicate' n x@ creates a Braun tree from @n@
-- copies of @x@.
--
-- prop> \(NonNegative n) -> size (replicate n ()) == n
replicate :: Int -> a -> Tree a
replicate m x = go m (const id)
  where
    go 0 k = k (Node x Leaf Leaf) Leaf
    go n k
      | odd n = go (pred n `div` 2) $ \s t -> k (Node x s t) (Node x t t)
      | otherwise = go (pred n `div` 2) $ \s t -> k (Node x s s) (Node x s t)

-- | /O(log n)/. Retrieve the element at the specified position,
-- raising an error if it's not present.
--
-- prop> \(NonNegative n) xs -> n < length xs ==> fromList xs ! n == xs !! n
(!) :: HasCallStack => Tree a -> Int -> a
(!) (Node x _ _) 0 = x
(!) (Node _ y z) i
    | odd i = y ! j
    | otherwise = z ! j
    where j = (i-1) `div` 2
(!) _ _ = error "Data.Tree.Braun.!: index out of range"

-- | /O(log n)/. Retrieve the element at the specified position, or
-- 'Nothing' if the index is out of range.
(!?) :: Tree a -> Int -> Maybe a
(!?) (Node x _ _) 0 = Just x
(!?) (Node _ y z) i
    | odd i = y !? j
    | otherwise = z !? j
    where j = (i-1) `div` 2
(!?) _ _ = Nothing

-- | Result of an upper bound operation.
data UpperBound a = Exact a
                  | TooHigh Int
                  | Finite

-- | Find the upper bound for a given element.
ub :: (a -> b -> Ordering) -> a -> Tree b -> UpperBound b
ub f x t = go f x t 0 1
  where
    go _ _ Leaf !_ !_ = Finite
    go _ _ (Node hd _ ev) !n !k =
      case f x hd of
        LT -> TooHigh n
        EQ -> Exact hd
        GT -> go f x ev (n+2*k) (2*k)

-- | /O(log n)/. Returns the first element in the array and the rest
-- the elements, if it is nonempty, or 'Nothing' if it is empty.
--
-- >>> uncons empty
-- Nothing
--
-- prop> uncons (cons x xs) === Just (x,xs)
-- prop> unfoldr uncons (fromList xs) === xs
uncons :: Tree a -> Maybe (a, Tree a)
uncons (Node x Leaf Leaf) = Just (x, Leaf)
uncons (Node x y z) = Just (x, Node lp z q)
  where
    Just (lp,q) = uncons y
uncons Leaf = Nothing

-- | /O(log n)/. Returns the first element in the array and the rest
-- the elements, if it is nonempty, failing with an error if it is
-- empty.
--
-- prop> uncons' (cons x xs) === (x,xs)
uncons' :: HasCallStack => Tree a -> (a, Tree a)
uncons' (Node x Leaf Leaf) = (x, Leaf)
uncons' (Node x y z) = (x, Node lp z q)
  where
    (lp,q) = uncons' y
uncons' Leaf = error "Data.Tree.Braun.uncons': empty tree"

-- | /O(log n)/. Append an element to the beginning of the Braun tree.
--
-- prop> uncons' (cons x xs) === (x,xs)
cons :: a -> Tree a -> Tree a
cons x Leaf = Node x Leaf Leaf
cons x (Node y p q) = Node x (cons y q) p

-- | /O(log n)/. Get all elements except the first from the Braun
-- tree. Returns an empty tree when called on an empty tree.
--
-- >>> tail empty
-- Leaf
--
-- prop> tail (cons x xs) === xs
-- prop> tail (cons undefined xs) === xs
tail :: Tree a -> Tree a
tail (Node _ Leaf Leaf) = Leaf
tail (Node _ y z) = Node lp z q
  where
    (lp,q) = uncons' y
tail Leaf = Leaf

-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.List (unfoldr)
-- >>> import qualified Data.Tree.Binary as Binary
-- >>> :{
-- instance Arbitrary a => Arbitrary (Tree a) where
--   arbitrary = fmap fromList arbitrary
--   shrink = fmap fromList . shrink . toList
-- :}
