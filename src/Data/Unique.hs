module Data.Unique where

import           Data.Braun.Sized (Braun(..))
import qualified Data.Braun.Sized as Braun
import           Data.Tree (Tree(..))

data Set a =
    Set {-# UNPACK #-} !Int
        (Braun (Braun a))

empty :: Set a
empty = Set 0 (Braun 0 Leaf)

sizes :: [Int]
sizes =
    [ max 1 (round (j * sqrt (logBase 2 j)))
    | i <- [1 ..]
    , let j = fromIntegral (i :: Int) :: Double ]

fromList :: [a] -> Set a
fromList xs =
  let n = length xs
      takeGroups [] _ = []
      takeGroups xs (k:ks) =
        let (y,ys) = splitAt k xs
        in y:takeGroups ys ks
      ys = Braun.fromList $ map Braun.fromList $ takeGroups xs sizes
  in Set n ys

comp :: Ord a => a -> Braun a -> Ordering
comp y b = let (h,_) = Braun.popFront b
           in compare y h

insert :: Ord a => a -> Set a -> Set a
insert x (Set 0 _) = Set 1 (Braun.fromList [Braun.fromList [x]])
insert x (Set n xs) =
  let ltx y = comp x y == LT
      (lte,gt) = break ltx $ Braun.toList xs
      final ps = let qs = fixupList ps sizes
                     m = sum $ map Braun.size qs
                 in Set m (Braun.fromList qs)
  in final $
     case (reverse lte,gt) of
       ([],gt1:gts) -> (Braun.pushFront x gt1):gts
       (eq:rev_lt,_) -> (reverse rev_lt) ++ [Braun.insert compare x eq] ++ gt

delete :: Ord a => a -> Set a -> Set a
delete x (Set 0 _) = empty
delete x (Set n xs) =
  let ltx y = comp x y == LT
      (lte,gt) = break ltx $ Braun.toList xs
      final ps = let qs = fixupList ps sizes
                     m = sum $ map Braun.size qs
                 in Set m (Braun.fromList qs)
  in final $
     case reverse lte of
       [] -> gt
       (eq:rev_lt) -> (reverse rev_lt) ++ [Braun.delete compare x eq] ++ gt


fixupList :: [Braun a] -> [Int] -> [Braun a]
fixupList [] _ = []
fixupList [x] _ = 
  if Braun.size x == 0
  then []
  else [x]
fixupList (x:y:ys) (z:zs) =
  case compare (Braun.size x) z of
    EQ -> x:(fixupList (y:ys) zs)
    LT -> let (p,ps) = Braun.popFront y
          in fixupList ((Braun.pushBack p x):ps:ys) (z:zs)
    GT -> let (q,qs) = Braun.popBack x
          in fixupList (qs:(Braun.pushFront q y):ys) (z:zs)
