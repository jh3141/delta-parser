module Main where

import Test.Tasty
import Test.Tasty.HUnit

import qualified ATNTests
import qualified DFATests
import qualified AutomataCacheTests

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
            [
                testGroup "ATN" ATNTests.allTests,
                testGroup "DFA" DFATests.allTests,
                testGroup "Automata Cache" AutomataCacheTests.allTests
            ]
