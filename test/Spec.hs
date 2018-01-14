{-# OPTIONS_GHC -fno-warn-orphans #-}

import           Control.Applicative
import           Data.Tree.Binary
import           Test.DocTest
import           Test.QuickCheck
import           Test.QuickCheck.Checkers
import           Test.QuickCheck.Classes
import           Data.Functor.Classes
import qualified Data.Tree.Braun as Braun

instance Arbitrary a =>
         Arbitrary (Tree a) where
    arbitrary = sized go
      where
        go 0 = pure Leaf
        go n
          | n <= 0 = pure Leaf
          | otherwise = oneof [pure Leaf, liftA3 Node arbitrary sub sub]
          where
            sub = go (n `div` 2)
    shrink Leaf = []
    shrink (Node x l r) =
        Leaf : l : r :
        [ Node x' l' r'
        | (x',l',r') <- shrink (x, l, r) ]

instance (Show a, Eq a) =>
         EqProp (Tree a) where
    x =-= y =
        whenFail
            (putStrLn (drawBinaryTree x ++ "\n/=\n" ++ drawBinaryTree y))
            (x == y)

eq1Prop
    :: (Eq (f a), Eq1 f, Show (f a), Eq a)
    => Gen (f a) -> (f a -> [f a]) -> Property
eq1Prop arb shrnk =
    forAllShrink arb shrnk $
    \xs ->
         forAllShrink (oneof [pure xs, arb]) shrnk $
         \ys ->
              liftEq (==) xs ys === (xs == ys)

main :: IO ()
main = do
    quickCheck (eq1Prop (arbitrary :: Gen (Tree Int)) shrink)
    quickBatch
        (ord
             (\x ->
                   oneof [pure (x :: Tree Int), arbitrary]))
    quickBatch
        (ordRel
             (\x y ->
                   liftCompare compare x y /= GT)
             (\x ->
                   oneof [pure (x :: Tree Int), arbitrary]))
    quickCheck
        (\xs ->
              show (xs :: Tree Int) ===
              liftShowsPrec showsPrec showList 0 xs "")
    quickCheck
        (\xs ->
              Braun.size (fromList xs) === length (xs :: [Int]))
    quickBatch (monoid (Leaf :: Tree Int))
    doctest ["-isrc", "src/"]
