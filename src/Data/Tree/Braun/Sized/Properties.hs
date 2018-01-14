module Data.Tree.Braun.Sized.Properties where

import Data.Tree.Braun.Sized

validSize :: Braun a -> Bool
validSize (Braun n xs) = n == length xs
