{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE DeriveFoldable #-}

module Data.Unique where

import qualified Data.Braun       as Unsized
import           Data.Braun.Sized (Braun (..))
import qualified Data.Braun.Sized as Braun
import           Data.Tree        (Tree (..))

-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.List (sort,nub)
-- >>> let shuffleProp f = (arbitrary :: Gen [Int]) >>= \xs -> shuffle xs >>= \ys -> pure (f xs ys)

data Set a =
    Set {-# UNPACK #-} !Int
        (Braun (Braun a)) deriving (Eq, Show, Foldable)

type Builder a b c d e = Int -> Int -> Int -> (Braun.Builder a (Braun a) (Braun a) -> Braun.Builder (Braun a) d e -> Int -> b) -> c

unSet (Set _ xs) = xs
sizeS (Set n _) = n

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

sizes :: [Int]
sizes =
    [ max 1 (round (j * sqrt (logBase 2 j)))
    | i <- [1 ..]
    , let j = fromIntegral (i :: Int) :: Double ]

-- |
--
-- prop> length xs === sizeS (fromList xs)
-- prop> all Braun.validSize (unSet (fromList xs))
-- prop> Braun.validSize (unSet (fromList xs))
-- prop> Unsized.isBraun (tree (unSet (fromList xs)))
-- prop> all (Unsized.isBraun . tree) (unSet (fromList xs))
fromList :: [a] -> Set a
fromList xs = runB (foldr consB nilB xs)

comp :: Ord a => a -> Braun a -> Ordering
comp y b = let (h,_) = Braun.popFront b
           in compare y h

ltc :: Ord a => a -> Braun a -> Bool
ltc x y = comp x y == LT

-- |
--
-- prop> shuffleProp (\xs ys -> foldr insert empty xs == foldr insert empty ys)
insert :: Ord a => a -> Set a -> Set a
insert x (Set 0 _) = Set 1 (Braun.fromList [Braun.fromList [x]])
insert x (Set _ xs) =
    let (lte,gt) = break (ltc x) $ Braun.toList xs
        final ps =
            let qs = fixupList ps sizes
                m = sum $ map Braun.size qs
            in Set m (Braun.fromList qs)
    in final $
       case (reverse lte, gt) of
           ([],gt1:gts) -> Braun.pushFront x gt1 : gts
           (eq:rev_lt,_) ->
               reverse rev_lt ++ [Braun.insert compare x eq] ++ gt

delete :: Ord a => a -> Set a -> Set a
delete _ (Set 0 _) = empty
delete x (Set _ xs) =
  let (lte,gt) = break (ltc x) $ Braun.toList xs
      final ps = let qs = fixupList ps sizes
                     m = sum $ map Braun.size qs
                 in Set m (Braun.fromList qs)
  in final $
     case reverse lte of
       []          -> gt
       (eq:rev_lt) -> reverse rev_lt ++ [Braun.delete compare x eq] ++ gt


fixupList :: [Braun a] -> [Int] -> [Braun a]
fixupList [] _ = []
fixupList [x] _ =
  if Braun.size x == 0
  then []
  else [x]
fixupList (x:y:ys) (z:zs) =
  case compare (Braun.size x) z of
    EQ -> x:fixupList (y:ys) zs
    LT -> let (p,ps) = Braun.popFront y
          in fixupList (Braun.pushBack p x:ps:ys) (z:zs)
    GT -> let (q,qs) = Braun.popBack x
          in fixupList (qs:Braun.pushFront q y:ys) (z:zs)
