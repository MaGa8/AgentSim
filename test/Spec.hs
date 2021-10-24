
import Test.QuickCheck

import BinTreeTest
import MultiRangeTreeTest

main :: IO ()
main = do
  testBinTree
  testMultiRangeTree
  return ()
