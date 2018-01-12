{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE Safe               #-}

-- | A simple, generic binary tree and some operations.
module Data.Tree
  (Tree(..)
  ,foldTree
  ,unfoldTree
  ,replicateTree
  ,replicateA
  ,treeFromList
  ,zygoTree
  ,drawBinaryTree)
  where

import           Control.DeepSeq      (NFData (..))
import           Data.Data            (Data)
import           Data.Functor.Classes
import           Data.Monoid
import           Data.Typeable        (Typeable)
import           GHC.Generics         (Generic, Generic1)

import           Data.Bifunctor
import           Data.Bool
import           Data.Function

import           Data.Functor.Identity

-- $setup
-- >>> import Test.QuickCheck

-- | A simple binary tree for use in some of the heaps.
data Tree a
    = Leaf
    | Node a
           (Tree a)
           (Tree a)
    deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable,Typeable
             ,Generic,Generic1,Data)

instance NFData a =>
         NFData (Tree a) where
    rnf Leaf         = ()
    rnf (Node x l r) = rnf x `seq` rnf l `seq` rnf r

instance Eq1 Tree where
    liftEq _ Leaf Leaf = True
    liftEq eq (Node x xl xr) (Node y yl yr) =
        eq x y && liftEq eq xl yl && liftEq eq xr yr
    liftEq _ _ _ = False

instance Ord1 Tree where
    liftCompare _ Leaf Leaf = EQ
    liftCompare cmp (Node x xl xr) (Node y yl yr) =
        cmp x y <> liftCompare cmp xl yl <> liftCompare cmp xr yr
    liftCompare _ Leaf _ = LT
    liftCompare _ _ Leaf = GT

instance Show1 Tree where
    liftShowsPrec s _ = go where
      go _ Leaf = showString "Leaf"
      go d (Node x l r)
        = showParen (d >= 11)
        $ showString "Node "
        . s 11 x
        . showChar ' '
        . go 11 l
        . showChar ' '
        . go 11 r

instance Read1 Tree where
    liftReadsPrec r _ = go
      where
        go d ss =
            readParen
                (d > 11)
                (\xs ->
                      [ (Leaf, ys)
                      | ("Leaf",ys) <- lex xs ])
                ss ++
            readParen
                (d > 10)
                (\vs ->
                      [ (Node x lx rx, zs)
                      | ("Node",ws) <- lex vs
                      , (x,xs) <- r 11 ws
                      , (lx,ys) <- go 11 xs
                      , (rx,zs) <- go 11 ys ])
                ss

-- | Fold over a tree.
foldTree :: b -> (a -> b -> b -> b) -> Tree a -> b
foldTree b f = go where
  go Leaf         = b
  go (Node x l r) = f x (go l) (go r)

-- | A zygomorphism over a tree. Used if you want perform two folds
-- over a tree in one pass.
--
-- As an example, checking if a tree is balanced can be performed like
-- this using explicit recursion:
--
-- @
-- isBalanced :: 'Tree' a -> Bool
-- isBalanced 'Leaf' = True
-- isBalanced ('Node' _ l r)
--   = 'length' l == 'length' r && isBalanced l && isBalanced r
-- @
--
-- However, this algorithm performs several extra passes over the
-- tree. A more efficient version is much harder to read, however:
--
-- @
-- isBalanced :: Tree a -> Bool
-- isBalanced = snd . go where
--   go 'Leaf' = (0 :: Int,True)
--   go ('Node' _ l r) =
--       let (llen,lbal) = go l
--           (rlen,rbal) = go r
--       in (llen + rlen + 1, llen == rlen && lbal && rbal)
-- @
--
-- This same algorithm (the one pass version) can be expressed as a
-- zygomorphism:
--
-- @
-- isBalanced :: 'Tree' a -> Bool
-- isBalanced =
--     'zygoTree'
--         (0 :: Int)
--         (\\_ x y -> 1 + x + y)
--         True
--         go
--   where
--     go _ llen lbal rlen rbal = llen == rlen && lbal && rbal
-- @
zygoTree
    :: p
    -> (a -> p -> p -> p)
    -> b
    -> (a -> p -> b -> p -> b -> b)
    -> Tree a
    -> b
zygoTree p f1 b f = snd . go where
  go Leaf = (p,b)
  go (Node x l r) =
      let (lr1,lr) = go l
          (rr1,rr) = go r
      in (f1 x lr1 rr1, f x lr1 lr rr1 rr)

-- | Unfold a tree from a seed.
unfoldTree :: (b -> Maybe (a, b, b)) -> b -> Tree a
unfoldTree f = go where
  go = maybe Leaf (\(x,l,r) -> Node x (go l) (go r)) . f

-- | @'replicateTree' n a@ creates a tree of size @n@ filled @a@.
-- >>> putStr (drawBinaryTree (replicateTree 4 ()))
--     ()
--   ()  ()
-- ()
--
-- prop> length (replicateTree (getNonNegative n) ()) === getNonNegative n
replicateTree :: Int -> a -> Tree a
replicateTree n x = runIdentity (replicateA n (Identity x))

-- | @'replicateA' n a@ replicates the action @a@ @n@ times.
replicateA :: Applicative f => Int -> f a -> f (Tree a)
replicateA n x = go n
  where
    go m
      | m <= 0 = pure Leaf
      | even m = Node <$> x <*> r <*> go (d-1)
      | otherwise = Node <$> x <*> r <*> r
      where
        d = m `div` 2
        r = go d
{-# SPECIALIZE replicateA :: Int -> Identity a -> Identity (Tree a) #-}

instance Monoid (Tree a) where
    mappend Leaf y         = y
    mappend (Node x l r) y = Node x l (mappend r y)
    mempty = Leaf

-- | Construct a tree from a list, putting each even-positioned
-- element to the left.
treeFromList :: [a] -> Tree a
treeFromList [] = Leaf
treeFromList (x:xs) = uncurry (Node x `on` treeFromList) (pairs xs) where
  pairs ys = foldr f (const ([],[])) ys True
  f e a b = bool first second b (e:) (a (not b))

-- | Pretty-print a tree.
--
-- >>> putStr (drawBinaryTree (treeFromList [1..7]))
--    1
--  3   2
-- 7 5 6 4
drawBinaryTree :: Show a => Tree a -> String
drawBinaryTree = foldr (. (:) '\n') "" . snd . foldTree (0, []) f
  where
    f el (llen,lb) (rlen,rb) =
        ( llen + rlen + xlen
        , pad llen . (xshw ++) . pad rlen :
          zipLongest (pad llen) (pad rlen) join' lb rb)
      where
        xshw = show el
        xlen = length xshw
        join' x y = x . pad xlen . y
    pad 0 = id
    pad n = (' ' :) . pad (n - 1)

zipLongest :: a -> b -> (a -> b -> c) -> [a] -> [b] -> [c]
zipLongest ldef rdef fn = go
  where
    go (x:xs) (y:ys) = fn x y : go xs ys
    go [] ys = map (fn ldef) ys
    go xs [] = map (`fn` rdef) xs
