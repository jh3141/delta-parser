module AutomataCacheTests (allTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Text.Parser.ALLStar

allTests :: [TestTree]
allTests =
    [
        testCase "Cache is initialized without an ATN" $ do
            cache <- mkCache
            assertBool "should not have had an ATN" $ not (isATNAvailable cache),
        testCase "Cache is initialized without a DFA" $ do
            cache <- mkCache
            assertBool "should not have had a DFA" $ not (isDFAAvailable cache)
    ]
