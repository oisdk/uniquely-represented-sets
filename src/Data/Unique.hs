{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE DeriveFoldable #-}

module Data.Unique where

import           Data.Braun.Sized (Braun (Braun))
import qualified Data.Braun.Sized as Braun
import           Data.Tree        (Tree (..))
import           GHC.Base         (build)
-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.List (sort,nub)
-- >>> import qualified Data.Braun as Unsized
-- >>> let shuffleProp f = (arbitrary :: Gen [Int]) >>= \xs -> shuffle xs >>= \ys -> pure (f xs ys)
-- >>> let safeInit xs = if null xs then [] else init xs
-- >>> let fromListIns xs = foldr insert empty (xs :: [Int])

data Set a = Set
    { size :: {-# UNPACK #-} !Int
    , tree :: Braun (Braun a)
    } deriving (Eq,Show,Foldable)

type Builder a b c d e = Int -> Int -> Int -> (Braun.Builder a (Braun a) (Braun a) -> Braun.Builder (Braun a) d e -> Int -> b) -> c

szfn :: Int -> Int
szfn i = max 1 (round (j * sqrt (logBase 2 j)))
  where
    !j = toEnum i :: Double

consB :: a -> Builder a b c d e -> Builder a b c d e
consB e a !k 1 !s p =
    a
        (k + 1)
        (szfn k)
        (s + 1)
        (\ys zs ->
              p Braun.nilB (Braun.consB (Braun.runB (Braun.consB e ys)) zs))
consB e a !k !i !s p = a k (i - 1) (s + 1) (p . Braun.consB e)
{-# INLINE consB #-}

nilB :: Builder a b b c c
nilB _ _ s p = p Braun.nilB Braun.nilB s
{-# INLINE nilB #-}

runB :: Builder a (Set a) (Set a) (Braun (Braun a)) (Braun (Braun a)) -> Set a
runB xs = xs 1 1 0 (\_ r s -> Set s (Braun.runB r))
{-# INLINE runB #-}

empty :: Set a
empty = Set 0 (Braun 0 Leaf)
{-# INLINE empty #-}

singleton :: a -> Set a
singleton x = Set 1 (Braun 1 (Node (Braun 1 (Node x Leaf Leaf)) Leaf Leaf))
{-# INLINE singleton #-}

-- |
--
-- prop> toList (fromList xs) === xs
toList :: Set a -> [a]
toList (Set _ xs) = build (\c n -> foldr (flip (foldr c)) n xs)
{-# INLINABLE toList #-}


-- |
--
-- prop> length xs === size (fromList xs)
-- prop> all Braun.validSize (tree (fromList xs))
-- prop> Braun.validSize (tree (fromList xs))
-- prop> Unsized.isBraun (Braun.tree (tree (fromList xs)))
-- prop> all (Unsized.isBraun . Braun.tree) (tree (fromList xs))
-- prop> validSizes (fromList xs)
fromList :: [a] -> Set a
fromList xs = runB (foldr consB nilB xs)
{-# INLINABLE fromList #-}

validSizes :: Set a -> Bool
validSizes (Set _ b) = null xs || it && re where
  xs = Braun.toList b
  it = and $ zipWith (\x y -> Braun.size x == szfn y) (safeInit xs) [1..]
  safeInit [] = []
  safeInit ys = init ys
  re = Braun.size (last xs) <= szfn (length xs)

-- |
--
-- >>> toList (foldr insert empty [3,1,2,5,4,3,6])
-- [1,2,3,4,5,6]
--
-- prop> length (nub xs) === size (fromListIns xs)
-- prop> all Braun.validSize (tree (fromListIns xs))
-- prop> Braun.validSize (tree (fromListIns xs))
-- prop> Unsized.isBraun (Braun.tree (tree (fromListIns xs)))
-- prop> all (Unsized.isBraun . Braun.tree) (tree (fromListIns xs))
-- prop> validSizes (fromListIns xs)
-- prop> shuffleProp (\xs ys -> foldr insert empty xs == foldr insert empty ys)
-- prop> shuffleProp (\xs ys -> fromList (sort (nub xs)) === foldr insert empty ys)
insert :: Ord a => a -> Set a -> Set a
insert = insertBy compare

insertBy :: (a -> a -> Ordering) -> a -> Set a -> Set a
insertBy _ x (Set 0 _) = singleton x
insertBy cmp x (Set _ xs) =
    let final ps =
            let qs = fixupList ps
                m = sum $ map Braun.size qs
            in Set m (Braun.fromList qs)
        ys = Braun.toList xs
    in 
       case breakThree (Braun.ltRoot cmp x) (Braun.toList xs) of
           Nothing -> case ys of (y:yys) -> final (Braun.cons x y : yys)
           Just (lt,eq,gt) -> final (lt ++ [Braun.insertBy cmp x eq] ++ gt)

deleteBy :: (a -> a -> Ordering) -> a -> Set a -> Set a
deleteBy _ _ (Set 0 _) = empty
deleteBy cmp x (Set _ xs) =
  let (lte,gt) = break (Braun.ltRoot cmp x) $ Braun.toList xs
      final ps = let qs = fixupList ps
                     m = sum $ map Braun.size qs
                 in Set m (Braun.fromList qs)
  in final $
     case reverse lte of
       []          -> gt
       (eq:rev_lt) -> reverse rev_lt ++ [Braun.deleteBy cmp x eq] ++ gt


fixupList :: [Braun a] -> [Braun a]
fixupList = go 1 where
  go !_ [] = []
  go !i [x] = case compare (Braun.size x) (szfn i) of
    LT | Braun.size x == 0 -> []
    GT -> let (q,qs) = Braun.unsnoc' x in [qs, Braun.Braun 1 (Node q Leaf Leaf)]
    _ -> [x]
  go !i (x:y:ys) =
    case compare (Braun.size x) (szfn i) of
      EQ -> x : go (i+1) (y:ys)
      LT -> let (p,ps) = Braun.uncons' y
            in Braun.pushBack p x : go (i+1) (ps:ys)
      GT -> let (q,qs) = Braun.unsnoc' x
            in qs : go (i+1) (Braun.cons q y:ys)

unsnocList :: [a] -> Maybe (a, [a])
unsnocList [] = Nothing
unsnocList (x:xs) = Just (unsnocList' x xs)
  where
    unsnocList' y [] = (y, [])
    unsnocList' y (z:zs) = (e, y : ys)
      where
        (e,ys) = unsnocList' z zs

breakThree :: (a -> Bool) -> [a] -> Maybe ([a], a, [a])
breakThree _ [] = Nothing
breakThree p (x:xs)
    | p x = Nothing
    | otherwise = Just (go p x xs)
    where
      go p' y zs@(z:zs')
          | p' z = ([],y,zs)
          | otherwise = let (xs',x',ys') = go p' z zs' in (y:xs',x',ys')
      go _ y [] = ([],y,[])
