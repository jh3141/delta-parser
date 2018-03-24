{-# LANGUAGE ScopedTypeVariables #-}
module ATNTests (allTests) where

import qualified Data.IntMap as IM
import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.QuickCheck
import Text.Parser.ALLStar



allTests :: [TestTree]
allTests =
    [
        testCase "An empty ATN has no states" $
            atnStateCount emptyATN @?= 0,
        testCase "An empty ATN has an empty state production index" $
            IM.size (atnStateProductionIndex emptyATN) @?= 0,
        testCase "An empty ATN has an empty non terminal state map" $
            M.size (atnNonTerminalStates emptyATN) @?= 0,
        testCase "An empty ATN has an empty production start state map" $
            IM.size (atnProductionStartState emptyATN) @?= 0,
        testCase "An empty ATN has an empty transition map" $
            IM.size (atnTransitionMap emptyATN) @?= 0,
        testCase "An empty ATN has an empty end state nonterminal map" $
            IM.size (atnEndStateNonTerminal emptyATN) @?= 0,
        testCase "Adding a non-terminal to an empty ATN creates 2 states" $
            let (atn, _) = atnAddOrFindNonTerminal "nonterm" emptyATN
             in atnStateCount atn @?= 2,
        testCase "atnAddOrFindNonTerminal with unknown nonterminal returns (0,1)" $ do
            let (_, (s, e)) = atnAddOrFindNonTerminal "nonterm" emptyATN
            assertEqual "start state should have been 0" 0 s
            assertEqual "end state should have been 1" 1 e,
        testCase "adding a second unknown nonterminal returns (2,3)" $ do
            let (atn, _) = atnAddOrFindNonTerminal "t1" emptyATN
            let (_, (s, e)) = atnAddOrFindNonTerminal "t2" atn
            assertEqual "start state should have been 2" 2 s
            assertEqual "end state should have been 3" 3 e,
        testCase "retrieving existing nonterminal retrieves old indices" $ do
            let (atn, _) = atnAddOrFindNonTerminal "t1" emptyATN
            let (_, (s, e)) = atnAddOrFindNonTerminal "t1" atn
            assertEqual "start state should have been 0" 0 s
            assertEqual "end state should have been 1" 1 e,
        testCase "retrieving existing nonterminal doesn't increase state count" $ do
            let (atn, _) = atnAddOrFindNonTerminal "t1" emptyATN
            let (atn2, _) = atnAddOrFindNonTerminal "t1" atn
            assertEqual "state count should have been 2" 2 $ atnStateCount atn2,
        testCase "added start state for a nonterminal is associated with it" $ do
            let (atn, (s, _)) = atnAddOrFindNonTerminal "nonterm" emptyATN
            let Just (Left (nt, _)) = IM.lookup s (atnStateProductionIndex atn)
            assertEqual "non terminal for state should have been 'nonterm'" "nonterm" nt,
        testCase "added start state for a nonterminal is a start state" $ do
            let (atn, (s, _)) = atnAddOrFindNonTerminal "nonterm" emptyATN
            let Just (Left (_, t)) = IM.lookup s (atnStateProductionIndex atn)
            assertEqual "type flag for state should have been False" False t,
        testCase "added stop state for a nonterminal is associated with it" $ do
            let (atn, (_, s)) = atnAddOrFindNonTerminal "nonterm" emptyATN
            let Just (Left (nt, _)) = IM.lookup s (atnStateProductionIndex atn)
            assertEqual "non terminal for state should have been 'nonterm'" "nonterm" nt,
        testCase "added stop state for a nonterminal is a stop state" $ do
            let (atn, (_, s)) = atnAddOrFindNonTerminal "nonterm" emptyATN
            let Just (Left (_, t)) = IM.lookup s (atnStateProductionIndex atn)
            assertEqual "type flag for state should have been True" True t,
        testCase "stop state is associated with correct nonterminal" $ do
            let (atn, (_, s)) = atnAddOrFindNonTerminal "nonterm" emptyATN
            assertEqual "incorrect entry for end state non terminal map"
                (Just "nonterm") (IM.lookup s $ atnEndStateNonTerminal atn),
        testProperty "existing states not modified when adding nonterminals" $
            \ (terminals :: [String]) ->
                let (atn, (s1, s2)) :: ATNWithNonTerminalState Char String Int = atnAddOrFindNonTerminal "x" emptyATN in
                let atn' = foldl (\ a t -> fst $ atnAddOrFindNonTerminal t a) atn terminals in
                let (_, (s3, s4)) = atnAddOrFindNonTerminal "x" atn' in
                True ==> (s3, s4) == (s1, s2)

    ]
