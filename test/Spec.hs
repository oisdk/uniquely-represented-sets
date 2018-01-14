{-# OPTIONS_GHC -fno-warn-orphans #-}

import           Control.Applicative
import           Data.Foldable
import           Data.Functor.Classes
import qualified Data.Set                         as Set
import qualified Data.Set.Unique                  as Unique
import qualified Data.Set.Unique.Properties       as Unique
import           Data.Tree.Binary
import qualified Data.Tree.Braun                  as Braun
import qualified Data.Tree.Braun.Sized            as Sized
import qualified Data.Tree.Braun.Sized.Properties as Sized
import           Test.DocTest
import           Test.QuickCheck
import           Test.QuickCheck.Checkers
import           Test.QuickCheck.Classes
import           Test.QuickCheck.Poly

toUniqOrdList :: Ord a => [a] -> [a]
toUniqOrdList = Set.toList . Set.fromList

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

instance Arbitrary a =>
         Arbitrary (Sized.Braun a) where
    arbitrary = fmap Sized.fromList arbitrary
    shrink = fmap Sized.fromList . shrink . toList

instance (Show a, Eq a) =>
         EqProp (Tree a) where
    x =-= y =
        whenFail
            (putStrLn (drawBinaryTree x ++ "\n/=\n" ++ drawBinaryTree y))
            (x == y)

instance (Arbitrary a, Ord a) =>
         Arbitrary (Unique.Set a) where
    arbitrary = fmap Unique.fromList arbitrary
    shrink = fmap Unique.fromList . shrink . toList

eq1Prop
    :: (Eq (f a), Eq1 f, Show (f a), Eq a)
    => Gen (f a) -> (f a -> [f a]) -> Property
eq1Prop arb shrnk =
    forAllShrink arb shrnk $
    \xs ->
         forAllShrink (oneof [pure xs, arb]) shrnk $
         \ys ->
              liftEq (==) xs ys === (xs == ys)

validSized :: Show a => Sized.Braun a -> Property
validSized br =
    whenFail
        (putStrLn
             ("Not a valid Braun tree:\n" ++ drawBinaryTree (Sized.tree br)))
        (Sized.isBraun br) .&&.
    counterexample "Invalid size" (Sized.validSize br)

validUnique :: Show a => Unique.Set a -> Property
validUnique s =
    conjoin
        [ counterexample "sizes not in bounds" $ Unique.sizesInBound s
        , counterexample "subtrees not braun" $ Unique.allBraun s
        , counterexample "subtrees not correct sizes" $ Unique.allCorrectSizes s
        , counterexample "incorrect size" $ Unique.validSize s]

validSetOpsProp :: [OrdA] -> OrdA -> Unique.Set OrdA -> Property
validSetOpsProp xs x s =
    conjoin
        [ validUnique s
        , counterexample "after insert" $ validUnique (Unique.insert x s)
        , counterexample "after delete" $ validUnique (Unique.delete x s)
        , counterexample "after fromAscList" $ validUnique (Unique.fromAscList xs)
        ]

validOpsProp :: Show a => a -> Sized.Braun a -> Property
validOpsProp x br =
    conjoin
        [ validSized br
        , counterexample "after snoc" (validSized (Sized.snoc x br))
        , counterexample "after cons" (validSized (Sized.cons x br))
        , counterexample
              "after uncons"
              (conjoin $ fmap (validSized . snd) (toList (Sized.uncons br)))
        , counterexample
              "after unsnoc"
              (conjoin $ fmap (validSized . snd) (toList (Sized.uncons br)))]

setMemberProp :: Property
setMemberProp =
    property $
    do xs <- arbitrary :: Gen [OrdA]
       x <- arbitrary :: Gen OrdA
       ys <- shuffle (x : xs)
       pure
           (Unique.member x (Unique.fromList ys) &&
            not (Unique.member x (Unique.fromList (filter (x /=) ys))))

setShuffleProp :: Property
setShuffleProp = property $ do
    xs <- arbitrary :: Gen [OrdA]
    ys <- shuffle xs
    pure (Unique.fromList xs === Unique.fromList ys)

setFromListWithProp :: Property
setFromListWithProp = property $ do
    xs <- arbitrary :: Gen [OrdA]
    pure (Unique.fromList xs === Unique.fromListBy compare xs)


insertSizedProp :: [OrdA] -> Property
insertSizedProp xs =
    foldr (Sized.insertBy compare) Sized.empty xs ===
    Sized.fromList (toUniqOrdList xs)

deleteSizedProp :: OrdA -> [OrdA] -> Property
deleteSizedProp x xs = Sized.fromList setwo === deled .&&. validSized deled
  where
    setwi = toUniqOrdList (x : xs)
    setwo =
        toUniqOrdList
            [ y
            | y <- xs
            , y /= x ]
    deled = Sized.deleteBy compare x (Sized.fromList setwi)

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
    quickCheck (validOpsProp (1 :: Int))
    quickCheck insertSizedProp
    quickCheck deleteSizedProp
    quickCheck validSetOpsProp
    quickCheck setMemberProp
    quickCheck setShuffleProp
    quickCheck setFromListWithProp
    quickBatch (monoid (Leaf :: Tree Int))
    doctest ["-isrc", "src/"]
