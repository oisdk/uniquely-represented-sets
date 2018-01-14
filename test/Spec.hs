import Test.DocTest
import Test.QuickCheck
import Data.Tree.Binary


main :: IO ()
main = doctest ["-isrc", "src/"]
