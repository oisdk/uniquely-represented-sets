{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes          #-}

module Data.Braun where

import           Data.Tree (Tree (..), zygoTree)
import           GHC.Base  (build)
import           Prelude hiding (tail)

-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.List (unfoldr)
-- >>> :{
-- instance Arbitrary a => Arbitrary (Tree a) where
--   arbitrary = fmap fromList arbitrary
--   shrink = fmap fromList . shrink . toList
-- :}

-- |
--
-- prop> toList (fromList xs) == (xs :: [Int])
fromList :: [a] -> Tree a
fromList xs = runB (foldr consB nilB xs)
{-# INLINABLE fromList #-}

type Builder a b c = (Int -> Int -> (([Tree a] -> [Tree a] -> [Tree a]) -> [Tree a] -> b) -> c)

consB :: a -> Builder a b c -> Builder a b c
consB e a !k 1 p  = a (k*2) k (\ys zs -> p (\_ _ -> []) (runZip e ys zs (drop k zs)))
consB e a !k !m p = a k (m-1) (p . runZip e)
{-# INLINE consB #-}

nilB :: Builder a b b
nilB _ _ p = p (\_ _ -> []) [Leaf]
{-# INLINE nilB #-}

runB :: Builder a (Tree a) (Tree a) -> Tree a
runB b = b 1 1 (const head)
{-# INLINE runB #-}

runZip :: a
       -> ([Tree a] -> [Tree a] -> [Tree a])
       -> [Tree a]
       -> [Tree a]
       -> [Tree a]
runZip x a (y:ys) (z:zs) = Node x y    z    : a ys zs
runZip x a [] (z:zs)     = Node x Leaf z    : a [] zs
runZip x a (y:ys) []     = Node x y    Leaf : a ys []
runZip x a [] []         = Node x Leaf Leaf : a [] []
{-# NOINLINE runZip #-}

toListFB :: Tree a -> (a -> b -> b) -> b -> b
toListFB tr c n =
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
                      errorWithoutStackTrace "Data.Braun.toList: bug!"
                  leftChildren (Node _ Leaf _) _ = []
                  leftChildren (Node _ l _) a = l : a
                  leftChildren _ _ =
                      errorWithoutStackTrace "Data.Braun.toList: bug!"
                  root (Node x _ _) = x
                  root _ = errorWithoutStackTrace "Data.Braun.toList: bug!"
{-# INLINE toListFB #-}

toList :: Tree a -> [a]
toList tr = build (toListFB tr)
{-# INLINABLE toList #-}

-- |
--
-- prop> size (fromList xs) == length xs
size :: Tree a -> Int
size Leaf = 0
size (Node _ l r) = 1 + 2 * m + diff l m where
  m = size r
  diff Leaf 0 = 0
  diff (Node _ Leaf Leaf) 0 = 1
  diff (Node _ s t) k
      | odd k = diff s (k `div` 2)
      | otherwise = diff t ((k `div` 2) - 1)
  diff Leaf _ = errorWithoutStackTrace "Data.Braun.size: bug!"

-- |
--
-- prop> isBraun (fromList xs)
isBraun :: Tree a -> Bool
isBraun = zygoTree (0 :: Int) (\_ l r -> 1 + l + r) True alg
  where
    alg _ lsize lbrn rsize rbrn =
        lbrn && rbrn && (lsize == rsize || lsize - 1 == rsize)

-- |
--
-- prop> size (copy () (getNonNegative n)) == getNonNegative n
copy :: a -> Int -> Tree a
copy x = flip go (const id)
  where
    go 0 k = k (Node x Leaf Leaf) Leaf
    go n k
      | odd n = go (pred n `div` 2) $ \s t -> k (Node x s t) (Node x t t)
      | otherwise = go (pred n `div` 2) $ \s t -> k (Node x s s) (Node x s t)

-- |
--
-- prop> \(NonNegative n) xs -> n < length xs ==> fromList xs ! n == xs !! n
(!) :: Tree a -> Int -> a
(!) (Node x _ _) 0 = x
(!) (Node _ y z) i
    | odd i = y ! j
    | otherwise = z ! j
    where j = (i-1) `div` 2
(!) _ _ = error "Data.Braun.!: index out of range"

(!?) :: Tree a -> Int -> Maybe a
(!?) (Node x _ _) 0 = Just x
(!?) (Node _ y z) i
    | odd i = y !? j
    | otherwise = z !? j
    where j = (i-1) `div` 2
(!?) _ _ = Nothing

data UpperBound a = Exact a
                  | TooHigh Int
                  | Finite

ub :: (a -> b -> Ordering) -> a -> Tree b -> UpperBound b
ub f x t = go f x t 0 1
  where
    go _ _ Leaf !_ !_ = Finite
    go _ _ (Node hd _ ev) !n !k =
      case f x hd of
        LT -> TooHigh n
        EQ -> Exact hd
        GT -> go f x ev (n+2*k) (2*k)

-- |
--
-- prop> unfoldr uncons (fromList xs) == xs
uncons :: Tree a -> Maybe (a, Tree a)
uncons (Node x Leaf Leaf) = Just (x, Leaf)
uncons (Node x y z) = Just (x, Node lp z q)
  where
    (lp,q) = unconsSure y
    unconsSure (Node x' Leaf Leaf) = (x', Leaf)
    unconsSure (Node x' y' z') = (x', Node lp' z' q')
      where
        (lp',q') = unconsSure y'
    unconsSure Leaf = errorWithoutStackTrace "Data.Braun.uncons: bug!"
uncons Leaf = Nothing

uncons' :: Tree a -> (a, Tree a)
uncons' (Node x Leaf Leaf) = (x, Leaf)
uncons' (Node x y z) = (x, Node lp z q)
  where
    (lp,q) = uncons' y
uncons' Leaf = error "Data.Braun.uncons': empty tree"

-- |
--
-- prop> uncons' (cons x xs) === (x,xs)
cons :: a -> Tree a -> Tree a
cons x Leaf = Node x Leaf Leaf
cons x (Node y p q) = Node x (cons y q) p

-- |
--
-- >>> tail Leaf
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
