{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}

-- | This module provides a uniquely-represented Set type.
--
-- Uniquely represented sets means that elements inserted in any order
-- are represented by the same set. This makes it useful for
-- type-level programming, and some security applications.
module Data.Set.Unique
  (
   -- * Set type
   Set(..)
  ,
   -- * Construction
   fromList
  ,fromListBy
  ,empty
  ,singleton
  ,fromDistinctAscList
  ,
   -- ** Building
   Builder
  ,consB
  ,nilB
  ,runB
  ,
   -- * Modification
   insert
  ,insertBy
  ,delete
  ,deleteBy
  ,
   -- * Querying
   lookupBy
  ,member
  ,
   -- * Size invariant
   szfn)
  where

import           Control.DeepSeq       (NFData (rnf))
import           Data.Data             (Data)
import           Data.Foldable
import           Data.List             (sortBy)
import           Data.Maybe            (isJust)
import qualified Data.Set              as Set
import           Data.Tree.Binary      (Tree (..))
import           Data.Tree.Braun.Sized (Braun (Braun))
import qualified Data.Tree.Braun.Sized as Braun
import           Data.Typeable         (Typeable)
import           GHC.Base              (build)
import           GHC.Generics          (Generic, Generic1)

-- | A uniquely-represented set.
newtype Set a = Set
    { tree :: Braun (Braun a)
    } deriving (Show,Read,Eq,Ord,Functor,Typeable,Generic,Generic1,Data)

instance NFData a => NFData (Set a) where
    rnf (Set xs) = rnf xs

-- | A type suitable for building a 'Set' by repeated applications
-- of 'consB'.
type Builder a b c = Int -> Int -> (Braun.Builder a (Braun a) -> Braun.Builder (Braun a) b -> c) -> c

-- | The size invariant. The nth Braun tree in the set has size
-- szfn n.
szfn :: Int -> Int
szfn i = max 1 (round (j * sqrt (logBase 2 j)))
  where
    !j = toEnum i :: Double
{-# INLINE szfn #-}

-- | /O(n log n)/. Create a set from a list.
fromList :: Ord a => [a] -> Set a
fromList xs = runB (Set.foldr consB nilB (Set.fromList xs))
{-# INLINE fromList #-}

-- | /O(n log n)/. Create a set from a list, using the supplied
-- ordering function.
--
-- prop> fromListBy compare xs === fromList xs
fromListBy :: (a -> a -> Ordering) -> [a] -> Set a
fromListBy cmp xs = runB (foldr f (const nilB) (sortBy cmp xs) (const False))
  where
    f x a q
      | q x = zs
      | otherwise = consB x zs
      where
        zs = a ((EQ ==) . cmp x)

-- | /O(1)/. Push an element to the front of a 'Builder'.
consB :: a -> Builder a c d -> Builder a c d
consB e a !k 1 p =
    a
        (k + 1)
        (szfn k)
        (\ys zs ->
              p Braun.nilB (Braun.consB (Braun.runB (Braun.consB e ys)) zs))
consB e a !k !i p = a k (i - 1) (p . Braun.consB e)
{-# INLINE consB #-}

-- | An empty 'Builder'.
nilB :: Builder a b c
nilB _ _ p = p Braun.nilB Braun.nilB
{-# INLINE nilB #-}

-- | Convert a 'Builder' to a 'Set'.
runB :: Builder a (Braun (Braun a)) (Set a)-> Set a
runB xs = xs 1 1 (const (Set . Braun.runB))
{-# INLINE runB #-}

-- | The empty set.
empty :: Set a
empty = Set (Braun 0 Leaf)
{-# INLINE empty #-}

-- | Create a set with one element.
singleton :: a -> Set a
singleton x = Set (Braun 1 (Node (Braun 1 (Node x Leaf Leaf)) Leaf Leaf))
{-# INLINE singleton #-}

-- | 'toList' is /O(n)/.
--
-- prop> toList (fromDistinctAscList xs) === xs
instance Foldable Set where
    foldr f b (Set xs) = foldr (flip (foldr f)) b xs
    {-# INLINE foldr #-}
    toList (Set xs) = build (\c n -> foldr (flip (foldr c)) n xs)
    {-# INLINABLE toList #-}
    length (Set (Braun _ xs)) = foldl' (\a e -> a + Braun.size e) 0 xs

instance Traversable Set where
    traverse f (Set xs) = fmap Set ((traverse . traverse) f xs)

-- | /O(n)/. Create a set from a list of ordered, distinct elements.
--
-- prop> fromDistinctAscList (toList xs) === xs
fromDistinctAscList :: [a] -> Set a
fromDistinctAscList xs = runB (foldr consB nilB xs)
{-# INLINABLE fromDistinctAscList #-}

-- | /sqrt(n log n)/. Insert an element into the set.
--
-- >>> toList (foldr insert empty [3,1,2,5,4,3,6])
-- [1,2,3,4,5,6]
insert :: Ord a => a -> Set a -> Set a
insert = insertBy compare
{-# INLINE insert #-}

-- | /sqrt(n log n)/. Insert an element into the set, using the
-- supplied ordering function.
--
-- prop> insert x xs === insertBy compare x xs
insertBy :: (a -> a -> Ordering) -> a -> Set a -> Set a
insertBy cmp x pr@(Set xs) =
    case ys of
        [] -> singleton x
        (y:yys) ->
            case breakThree (Braun.ltRoot cmp x) ys of
                Nothing ->
                    Set (Braun.runB (foldr fixf fixb yys 1 (Braun.cons x y)))
                Just (lt,eq,i,gt)
                  | Braun.size eq == Braun.size new -> pr
                  | otherwise ->
                      Set
                          (Braun.runB
                               (foldr Braun.consB (foldr fixf fixb gt i new) lt))
                    where new = Braun.insertBy cmp x eq
  where
    ys = toList xs
    fixf z zs !i y =
        let (q,qs) = Braun.unsnoc' y
        in Braun.consB qs (zs (i + 1) (Braun.cons q z))
    {-# INLINE fixf #-}
    fixb !i y
      | Braun.size y > szfn i =
          let (q,qs) = Braun.unsnoc' y
          in Braun.consB qs (Braun.consB (Braun.singleton q) Braun.nilB)
      | otherwise = Braun.consB y Braun.nilB
    {-# INLINE fixb #-}
{-# INLINE insertBy #-}

-- | /sqrt(n log n)/. Delete an element from the set.
delete :: Ord a => a -> Set a -> Set a
delete = deleteBy compare

-- | /sqrt(n log n)/. Delete an element from the set, using the
-- supplied ordering function.
--
-- prop> delete x xs === deleteBy compare x xs
deleteBy :: (a -> a -> Ordering) -> a -> Set a -> Set a
deleteBy cmp x pr@(Set xs) =
    case breakThree (Braun.ltRoot cmp x) (toList xs) of
        Nothing -> pr
        Just (lt,eq,_,gt)
          | Braun.size eq == Braun.size new -> pr
          | otherwise -> Set (Braun.runB (foldr Braun.consB (foldr fixf fixb gt new) lt))
            where new = Braun.deleteBy cmp x eq
                  fixb (Braun _ Leaf) = Braun.nilB
                  fixb y = Braun.consB y Braun.nilB
                  fixf z zs y =
                      let (p,ps) = Braun.uncons' z
                      in Braun.snoc p y `Braun.consB` zs ps

-- | /O(log^2 n)/. Lookup an element according to the supplied
-- ordering function in the set.
lookupBy :: (a -> a -> Ordering) -> a -> Set a -> Maybe a
lookupBy cmp x (Set xs) = do
    ys <- Braun.glb (Braun.cmpRoot cmp) x xs
    y <- Braun.glb cmp x ys
    case cmp x y of
      EQ -> pure y
      _  -> Nothing

-- | /O(log^2 n)/. Find if an element is a member of the set.
member :: Ord a => a -> Set a -> Bool
member x xs = isJust (lookupBy compare x xs)
{-# INLINE member #-}

breakThree :: (a -> Bool) -> [a] -> Maybe ([a], a, Int, [a])
breakThree _ [] = Nothing
breakThree p (x:xs)
    | p x = Nothing
    | otherwise = Just (go 1 id p x xs)
    where
      go !i k p' y zs@(z:zs')
          | p' z = (k [],y,i, zs)
          | otherwise = go (i+1) (k . (y:)) p' z zs'
      go !i k _ y [] = (k [],y,i,[])
{-# INLINE breakThree #-}

-- $setup
-- >>> import Test.QuickCheck
-- >>> :{
-- instance (Arbitrary a, Ord a) =>
--          Arbitrary (Set a) where
--     arbitrary = fmap fromList arbitrary
--     shrink = fmap fromList . shrink . toList
-- :}
