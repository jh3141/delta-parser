module DFATests (allTests) where

import Test.Tasty
import Test.Tasty.HUnit

allTests :: [TestTree]
allTests =
    [
        testCase "DFA Tests are run" $ 1 @?= 1
    ]
