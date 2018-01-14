module Data.Tree.Braun.Sized.Properties where

import Data.Tree.Braun.Sized
import qualified Data.Tree.Braun.Properties as Unsized

-- | Returns True iff the stored size in the Braun tree is its actual
-- size.
validSize :: Braun a -> Bool
validSize (Braun n xs) = n == length xs

-- | Returns True iff the tree is a proper Braun tree.
isBraun :: Braun a -> Bool
isBraun (Braun _ xs) = Unsized.isBraun xs
