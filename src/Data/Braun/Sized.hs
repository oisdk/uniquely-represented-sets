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

pushBack :: a -> Braun a -> Braun a
pushBack x (Braun 0 Leaf) = Braun 1 (Node x Leaf Leaf)
pushBack x (Braun n (Node y z w))
  | even n = Braun (n + 1) (Node y z (tree (pushBack x (Braun (m - 1) w))))
  | otherwise = Braun (n + 1) (Node y (tree (pushBack x (Braun m z))) w)
  where
    m = n `div` 2
pushBack _ (Braun _ Leaf) = errorWithoutStackTrace "Data.Braun.Sized.pushBack: bug!"

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
-- prop> foldr (insert compare) (Braun 0 Leaf) xs == fromList (sort (nub xs))
insert :: (a -> a -> Ordering) -> a -> Braun a -> Braun a
insert cmp x b@(Braun s xs) =
    case break
             (\y ->
                   cmp x y /= GT)
             (Unsized.toList xs) of
        (_,[]) -> pushBack x b
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

delete :: (a -> a -> Ordering) -> a -> Braun a -> Braun a
delete cmp x b@(Braun s xs) =
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

pushFront :: a -> Braun a -> Braun a
pushFront x' (Braun n xs) = Braun (n+1) (go x' xs) where
  go x Leaf         = Node x Leaf Leaf
  go x (Node y p q) = Node x (go y q) p

popFront :: Braun a -> (a, Braun a)
popFront (Braun n p) = (x', Braun (n-1) np) where
  (x',np) = go p
  go (Node x Leaf Leaf) = (x,Leaf)
  go (Node x y z) = (x, Node lp z q) where
    (lp,q) = go y
  go _ = errorWithoutStackTrace "Data.Braun.Sized.popFront: bug!"

-- |
--
-- unfoldr unsnoc (fromList xs) === reverse xs
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
unsnoc' (Braun _ Leaf) = error "Data.Braun.Sized.unsnoc': empty tree"
unsnoc' (Braun s tr) = (lst,Braun (s-1) ntr) where
  (lst,ntr) = go s tr
  go !n (Node x Leaf Leaf) = (x, Leaf)
  go !n (Node x y z)
    | odd n = case go m z of
        (p, q) -> (p, (Node x y q))
    | otherwise = case go  m y of
        (p, q) -> (p, (Node x q z))
    where
      m = n `div` 2
  go !_ Leaf = errorWithoutStackTrace "Data.Braun.Sized.unsnoc': bug!"
