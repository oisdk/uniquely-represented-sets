{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes    #-}

module Data.Braun.Sized where

import           Data.Braun      (UpperBound (..))
import qualified Data.Braun      as Unsized
import           Data.Tree       (Tree (..))

import           Control.DeepSeq (NFData (rnf))

-- $setup
-- >>> import Data.List (sort, nub, unfoldr)
-- >>> import Test.QuickCheck
-- >>> :{
-- instance Arbitrary a => Arbitrary (Braun a) where
--   arbitrary = fmap fromList arbitrary
--   shrink = fmap fromList . shrink . toList
-- :}

data Braun a = Braun
    { size :: {-# UNPACK #-} !Int
    , tree :: Tree a
    } deriving (Eq, Show, Functor)

instance NFData a => NFData (Braun a) where
    rnf (Braun _ tr) = rnf tr

instance Foldable Braun where
    foldr f b (Braun _ xs) = Unsized.toListFB xs f b

validSize :: Braun a -> Bool
validSize (Braun n xs) = n == length xs

snoc :: a -> Braun a -> Braun a
snoc x (Braun 0 Leaf) = Braun 1 (Node x Leaf Leaf)
snoc x (Braun n (Node y z w))
  | even n = Braun (n + 1) (Node y z (tree (snoc x (Braun (m - 1) w))))
  | otherwise = Braun (n + 1) (Node y (tree (snoc x (Braun m z))) w)
  where
    m = n `div` 2
snoc _ (Braun _ Leaf) = errorWithoutStackTrace "Data.Braun.Sized.snoc: bug!"

type Builder a b c = (Int -> Int -> Int -> (([Tree a] -> [Tree a] -> [Tree a]) -> [Tree a] -> Int -> b) -> c)

consB :: a -> Builder a b c -> Builder a b c
consB e a !k 1  !s p = a (k*2) k (s+1) (\ys zs -> p (\_ _ -> []) (Unsized.runZip e ys zs (drop k zs)))
consB e a !k !m !s p = a k (m-1) (s+1) (p . Unsized.runZip e)
{-# INLINE consB #-}

nilB :: Builder a b b
nilB _ _ s p = p (\_ _ -> []) [Leaf] s
{-# INLINE nilB #-}

runB :: Builder a (Braun a) (Braun a) -> Braun a
runB xs = xs 1 1 0 (const (flip Braun . head))
{-# INLINE runB #-}

-- |
--
-- prop> size (fromList xs) == length xs
fromList :: [a] -> Braun a
fromList xs = runB (foldr consB nilB xs)
{-# INLINABLE fromList #-}

empty :: Braun a
empty = Braun 0 Leaf

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
cmpRoot _ _ _ = error "Data.Braun.Sized.compRoot: empty tree"
{-# INLINE cmpRoot #-}

ltRoot :: (a -> b -> Ordering) -> a -> Braun b -> Bool
ltRoot cmp x (Braun _ (Node y _ _)) = cmp x y == LT
ltRoot _ _ _ = error "Data.Braun.ltRoot: empty tree"
{-# INLINE ltRoot #-}

gtRoot :: (a -> b -> Ordering) -> a -> Braun b -> Bool
gtRoot cmp x (Braun _ (Node y _ _)) = cmp x y == GT
gtRoot _ _ _ = error "Data.Braun.gtRoot: empty tree"
{-# INLINE gtRoot #-}

lteRoot :: (a -> b -> Ordering) -> a -> Braun b -> Bool
lteRoot cmp x (Braun _ (Node y _ _)) = cmp x y /= GT
lteRoot _ _ _ = error "Data.Braun.ltRoot: empty tree"
{-# INLINE lteRoot #-}
-- |
--
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

-- |
--
-- prop> Unsized.isBraun (tree (snd (unsnoc' (fromList (1:xs)))))
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
unsnoc' (Braun _ Leaf) = error "Data.Braun.Sized.unsnoc': empty tree"
