{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}

module Data.Tree.Braun.Sized
  (-- * Braun type
  Braun(..)
  -- * Construction
  ,fromList
  ,empty
  ,singleton
  -- ** Building
  ,Builder
  ,consB
  ,nilB
  ,runB
  -- * Modification
  -- ** At ends
  ,snoc
  ,unsnoc
  ,unsnoc'
  ,cons
  ,uncons
  ,uncons'
  -- ** As set
  ,insertBy
  ,deleteBy
  -- * Consuming
  ,toList
  -- * Querying
  ,glb
  ,cmpRoot
  ,ltRoot
  )
  where

import           Data.Tree.Binary         (Tree (..))
import           Data.Tree.Braun          (UpperBound (..))
import qualified Data.Tree.Braun          as Unsized
import           Data.Tree.Braun.Internal (zipLevels)

import           Control.DeepSeq          (NFData (rnf))
import           Data.Data                (Data)
import           Data.Typeable            (Typeable)
import           GHC.Generics             (Generic, Generic1)

import           Control.Applicative      hiding (empty)

-- | A Braun tree which keeps track of its size.
data Braun a = Braun
    { size :: {-# UNPACK #-} !Int
    , tree :: Tree a
    } deriving (Show,Read,Eq,Ord,Functor,Typeable,Generic,Generic1
               ,Data)

instance NFData a => NFData (Braun a) where
    rnf (Braun _ tr) = rnf tr

instance Foldable Braun where
    foldr f b (Braun _ xs) = Unsized.foldrBraun xs f b
    length = size

instance Traversable Braun where
    traverse f (Braun n tr) = fmap k (Unsized.foldrBraun tr c b)
      where
        c = liftA2 Unsized.consB . f
        b = pure Unsized.nilB
        k = Braun n . Unsized.runB

-- | /O(log n)/. Append an item to the end of a Braun tree.
--
-- prop> x `snoc` fromList xs === fromList (xs ++ [x])
snoc :: a -> Braun a -> Braun a
snoc x (Braun 0 Leaf) = Braun 1 (Node x Leaf Leaf)
snoc x (Braun n (Node y z w))
  | even n = Braun (n + 1) (Node y z (tree (snoc x (Braun (m - 1) w))))
  | otherwise = Braun (n + 1) (Node y (tree (snoc x (Braun m z))) w)
  where
    m = n `div` 2
snoc _ (Braun _ Leaf) = errorWithoutStackTrace "Data.Tree.Braun.Sized.snoc: bug!"

-- | A type suitable for building a Braun tree by repeated applications
-- of 'consB'.
type Builder a b = (Int -> Int -> Int -> (([Tree a] -> [Tree a] -> [Tree a]) -> [Tree a] -> Int -> b) -> b)

-- | /O(1)/. Push an element to the front of a 'Builder'.
consB :: a -> Builder a b -> Builder a b
consB e a !k 1  !s p = a (k*2) k (s+1) (\ys zs -> p (\_ _ -> []) (zipLevels e ys zs (drop k zs)))
consB e a !k !m !s p = a k (m-1) (s+1) (p . zipLevels e)
{-# INLINE consB #-}

-- | An empty 'Builder'.
nilB :: Builder a b
nilB _ _ s p = p (\_ _ -> []) [Leaf] s
{-# INLINE nilB #-}

-- | Convert a 'Builder' to a Braun tree.
runB :: Builder a (Braun a) -> Braun a
runB xs = xs 1 1 0 (const (flip Braun . head))
{-# INLINE runB #-}

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
-- prop> toList (fromList xs) === xs
fromList :: [a] -> Braun a
fromList xs = runB (foldr consB nilB xs)
{-# INLINABLE fromList #-}

-- | A Braun tree with no elements.
empty :: Braun a
empty = Braun 0 Leaf
{-# INLINE empty #-}

-- | A Braun tree with one element.
singleton :: a -> Braun a
singleton x = Braun 1 (Node x Leaf Leaf)
{-# INLINE singleton #-}

-- |
--
-- prop> foldr (insertBy compare) (Braun 0 Leaf) xs == fromList (sort (nub xs))
insertBy :: (a -> a -> Ordering) -> a -> Braun a -> Braun a
insertBy cmp x b@(Braun s xs) =
    case break
             (\y ->
                   cmp x y /= GT)
             (Unsized.toList xs) of
        (_,[]) -> snoc x b
        (lt,gte@(y:_)) ->
            if cmp x y == EQ
                then b
                else Braun
                         (s + 1)
                         (Unsized.runB
                              (foldr
                                   Unsized.consB
                                   (Unsized.consB
                                        x
                                        (foldr Unsized.consB Unsized.nilB gte))
                                   lt))

-- |
--
-- prop> deleteBy compare x (fromList (nub (x : xs))) === fromList [ y | y <- nub xs, y /= x ]
-- prop> validSize (deleteBy compare x xs)
deleteBy :: (a -> a -> Ordering) -> a -> Braun a -> Braun a
deleteBy cmp x b@(Braun s xs) =
    case break
             (\y -> cmp x y /= GT)
             (Unsized.toList xs) of
        (_,[]) -> b
        (lt,y:gt) ->
            if cmp x y /= EQ
                then b
                else Braun
                         (s - 1)
                              (Unsized.runB (foldr Unsized.consB (foldr Unsized.consB Unsized.nilB gt) lt))

glb :: (a -> b -> Ordering) -> a -> Braun b -> Maybe b
glb _ _ (Braun _ Leaf) = Nothing
glb cmp x (Braun n ys@(Node h _ _)) =
    case cmp x h of
        LT -> Nothing
        EQ -> Just h
        GT ->
            case Unsized.ub cmp x ys of
                Exact ans -> Just ans
                Finite
                  | cmp x final == LT -> go 0 (n - 1)
                  | otherwise -> Just final
                    where final = ys Unsized.! (n - 1)
                TooHigh m -> go 0 m
  where
    go _ 0 = Nothing
    go i j
      | j <= i = Just $ ys Unsized.! (j - 1)
      | i + 1 == j = Just $ ys Unsized.! i
      | otherwise =
          case cmp x middle of
              LT -> go i k
              EQ -> Just middle
              GT -> go k j
      where
        k = (i + j) `div` 2
        middle = ys Unsized.! k

-- | 
toList :: Braun a -> [a]
toList (Braun _ xs) = Unsized.toList xs
{-# INLINABLE toList #-}

-- |
--
-- prop> uncons' (cons x xs) == (x,xs)
cons :: a -> Braun a -> Braun a
cons x (Braun n xs) = Braun (n+1) (Unsized.cons x xs)

-- |
--
-- prop> unfoldr uncons (fromList xs) == xs
uncons :: Braun a -> Maybe (a, Braun a)
uncons (Braun n tr) = (fmap.fmap) (Braun (n-1)) (Unsized.uncons tr)

uncons' :: Braun a -> (a, Braun a)
uncons' (Braun n tr) = fmap (Braun (n-1)) (Unsized.uncons' tr)

cmpRoot :: (a -> b -> Ordering) -> a -> Braun b -> Ordering
cmpRoot cmp x (Braun _ (Node y _ _)) = cmp x y
cmpRoot _ _ _ = error "Data.Tree.Braun.Sized.compRoot: empty tree"
{-# INLINE cmpRoot #-}

ltRoot :: (a -> b -> Ordering) -> a -> Braun b -> Bool
ltRoot cmp x (Braun _ (Node y _ _)) = cmp x y == LT
ltRoot _ _ _                        = error "Data.Tree.Braun.Sized.ltRoot: empty tree"
{-# INLINE ltRoot #-}

-- | /O(log n)/. Returns the last element in the list and the other
-- elements, if present, or 'Nothing' if the tree is empty.
--
-- >>> unsnoc empty
-- Nothing
--
-- prop> unsnoc (snoc x xs) === Just (x, xs)
-- prop> unfoldr unsnoc (fromList xs) === reverse xs
unsnoc :: Braun a -> Maybe (a, Braun a)
unsnoc (Braun _ (Node x Leaf Leaf)) = Just (x, Braun 0 Leaf)
unsnoc (Braun n (Node x y z))
  | odd n =
      let Just (p,Braun _ q) = unsnoc (Braun m z)
      in Just (p, Braun (n - 1) (Node x y q))
  | otherwise =
      let Just (p,Braun _ q) = unsnoc (Braun m y)
      in Just (p, Braun (n - 1) (Node x q z))
  where
    m = n `div` 2
unsnoc (Braun _ Leaf) = Nothing

-- | /O(log n)/. Returns the last element in the list and the other
-- elements, if present, or raises an error if the tree is empty.
--
-- prop> isBraun (tree (snd (unsnoc' (fromList (1:xs)))))
-- prop> fst (unsnoc' (fromList (1:xs))) == last (1:xs)
unsnoc' :: Braun a -> (a, Braun a)
unsnoc' (Braun _ (Node x Leaf Leaf)) = (x, Braun 0 Leaf)
unsnoc' (Braun n (Node x y z))
  | odd n =
      let (p,Braun _ q) = unsnoc' (Braun m z)
      in (p, Braun (n - 1) (Node x y q))
  | otherwise =
      let (p,Braun _ q) = unsnoc' (Braun m y)
      in (p, Braun (n - 1) (Node x q z))
  where
    m = n `div` 2
unsnoc' (Braun _ Leaf) = error "Data.Tree.Braun.Sized.unsnoc': empty tree"

-- $setup
-- >>> import Data.List (sort, nub, unfoldr)
-- >>> import Test.QuickCheck
-- >>> import Data.Tree.Braun.Properties
-- >>> import Data.Tree.Braun.Sized.Properties
-- >>> :{
-- instance Arbitrary a => Arbitrary (Braun a) where
--   arbitrary = fmap fromList arbitrary
--   shrink = fmap fromList . shrink . toList
-- :}
