import Test.DocTest
import Test.QuickCheck

main :: IO ()
main = doctest ["-isrc", "src/"]
