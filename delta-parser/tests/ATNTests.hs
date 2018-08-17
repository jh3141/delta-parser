{-# LANGUAGE ScopedTypeVariables #-}
module ATNTests (allTests) where

import qualified Data.IntMap as IM
import qualified Data.Map as M
import Data.Maybe

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.QuickCheck ()
import Text.Parser.ALLStar

inMap :: Ord k => k -> M.Map k a -> Bool
k `inMap` m = isJust $ M.lookup k m

allTests :: [TestTree]
allTests =
    [
        testCase "An empty ATN has no states" $
                 atnStateCount emptyATNCSI @?= 0,

        testCase "An empty ATN has an empty state production index" $
                 IM.size (atnStateProductionIndex emptyATNCSI) @?= 0,

        testCase "An empty ATN has an empty non terminal state map" $
                 M.size (atnNonTerminalStates emptyATNCSI) @?= 0,

        testCase "An empty ATN has an empty production start state map" $
                 IM.size (atnProductionStartState emptyATNCSI) @?= 0,

        testCase "An empty ATN has an empty transition map" $
                 IM.size (atnTransitionMap emptyATNCSI) @?= 0,

        testCase "An empty ATN has an empty end state nonterminal map" $
                 IM.size (atnEndStateNonTerminal emptyATNCSI) @?= 0,

        testCase "Adding a non-terminal to an empty ATN creates 2 states" $
                 let (atn, _) = atnAddOrFindNonTerminal "nonterm" emptyATNCSI
                 in atnStateCount atn @?= 2,

        testCase "atnAddOrFindNonTerminal with unknown nonterminal returns (0,1)" $ do
            let (_, (s, e)) = atnAddOrFindNonTerminal "nonterm" emptyATNCSI
            assertEqual "start state should have been 0" 0 s
            assertEqual "end state should have been 1" 1 e,

        testCase "adding a second unknown nonterminal returns (2,3)" $ do
            let (atn, _) = atnAddOrFindNonTerminal "t1" emptyATNCSI
            let (_, (s, e)) = atnAddOrFindNonTerminal "t2" atn
            assertEqual "start state should have been 2" 2 s
            assertEqual "end state should have been 3" 3 e,

        testCase "retrieving existing nonterminal retrieves old indices" $ do
            let (atn, _) = atnAddOrFindNonTerminal "t1" emptyATNCSI
            let (_, (s, e)) = atnAddOrFindNonTerminal "t1" atn
            assertEqual "start state should have been 0" 0 s
            assertEqual "end state should have been 1" 1 e,

        testCase "retrieving existing nonterminal doesn't increase state count" $ do
            let (atn, _) = atnAddOrFindNonTerminal "t1" emptyATNCSI
            let (atn2, _) = atnAddOrFindNonTerminal "t1" atn
            assertEqual "state count should have been 2" 2 $ atnStateCount atn2,

        testCase "added start state for a nonterminal is associated with it" $ do
            let (atn, (s, _)) = atnAddOrFindNonTerminal "nonterm" emptyATNCSI
            let Just (Left (nt, _)) = IM.lookup s (atnStateProductionIndex atn)
            assertEqual "non terminal for state should have been 'nonterm'" "nonterm" nt,

        testCase "added start state for a nonterminal is a start state" $ do
            let (atn, (s, _)) = atnAddOrFindNonTerminal "nonterm" emptyATNCSI
            let Just (Left (_, t)) = IM.lookup s (atnStateProductionIndex atn)
            assertEqual "type flag for state should have been False" False t,

        testCase "added stop state for a nonterminal is associated with it" $ do
            let (atn, (_, s)) = atnAddOrFindNonTerminal "nonterm" emptyATNCSI
            let Just (Left (nt, _)) = IM.lookup s (atnStateProductionIndex atn)
            assertEqual "non terminal for state should have been 'nonterm'" "nonterm" nt,

        testCase "added stop state for a nonterminal is a stop state" $ do
            let (atn, (_, s)) = atnAddOrFindNonTerminal "nonterm" emptyATNCSI
            let Just (Left (_, t)) = IM.lookup s (atnStateProductionIndex atn)
            assertEqual "type flag for state should have been True" True t,

        testCase "stop state is associated with correct nonterminal" $ do
            let (atn, (_, s)) = atnAddOrFindNonTerminal "nonterm" emptyATNCSI
            assertEqual "incorrect entry for end state non terminal map"
                (Just "nonterm") (IM.lookup s $ atnEndStateNonTerminal atn),

        testProperty "existing states not modified when adding nonterminals" $
            \ (nonterminals :: [String]) ->
                let (atn, (s1, s2)) = atnAddOrFindNonTerminal "x" emptyATNCSI in
                let atn' = foldl (\ a t -> fst $ atnAddOrFindNonTerminal t a) atn nonterminals in
                let (_, (s3, s4)) = atnAddOrFindNonTerminal "x" atn' in
                True ==> (s3, s4) == (s1, s2),

        testProperty "all added nonterminals have start and end states" $
            \ (nonterminals :: [String]) ->
                let atn = foldl (\ a t -> fst $ atnAddOrFindNonTerminal t a) emptyATNCSI nonterminals in
                all (`inMap` atnNonTerminalStates atn) nonterminals,

        testCase "adding a production start state increases state count by one" $ do
            let (atn, _) = atnAddProductionStartState 5 (emptyATNCSI,(1,2))
            assertEqual "state count" 1 (atnStateCount atn),

        testCase "adding a production start state yields appropriate state triple" $ do
            let (_, states) = atnAddProductionStartState 5 (emptyATNCSI {atnStateCount = 3},(1,2))
            assertEqual "working states" (3,2,0) states,

        testCase "epsilon edge for production start added" $ do
            let (atn, _) = atnAddProductionStartState 5 (emptyATNCSI {atnStateCount = 3},(1,2))
            let stateTransitions = IM.lookup 1 $ atnTransitionMap atn
            assertEqual "edges from state 1" (Just [(Epsilon, [3])]) (M.toList <$> stateTransitions),

        testCase "second production start for same non-terminal adds second epsilon" $ do
            let (atn, _) = atnAddProductionStartState 5 (emptyATNCSI {atnStateCount = 3},(1,2))
            let (atn', _) = atnAddProductionStartState 6 (atn, (1,2))
            let stateTransitions = IM.lookup 1 $ atnTransitionMap atn'
            assertEqual "edges from state 1" (Just [(Epsilon, [4, 3])]) (M.toList <$> stateTransitions),

        testCase "adding an empty predicate doesn't change the ATN" $ do
            let (origAtn, st) = atnAddProductionStartState 5 $ (emptyATNCSI { atnStateCount = 3 }, (1,2))
            let (atn, _) = atnAddProductionPredicate 5 Nothing (origAtn, st)
            assertEqual "atn compare to updated atn" origAtn atn,

        testCase "atnProductionStart retrives start state for given production" $ do
            let atn = addProductionToATN emptyATNCSI "nonterm" (Production 1 Nothing [Left 'h', Left 'i'])
            -- at this point, state 0 should be the start state for "nonterm", state 2 the start state for
            -- production 1, 3 the point after receiving 'h', 4 after 'i', and 1 the accept state for "nonterm".
            assertEqual "production start should have been 2" (Just 2) $ atnProductionStart atn 1,

        testCase "different start states for different productions of the same non-terminal" $ do
            let atn1 = addProductionToATN emptyATNCSI "nonterm" (Production 1 Nothing [Left 'h', Left 'i'])
            let atn = addProductionToATN atn1 "nonterm" (Production 2 Nothing [Left 'h', Left 'o'])
            assertEqual "production 1 should start on state 2" (Just 2) $ atnProductionStart atn 1
            assertEqual "production 2 should start on state 5" (Just 5) $ atnProductionStart atn 2,

        testCase "can find valid production from a single state" $ do
            let atn = addProductionToATN emptyATNCSI "nonterm" (Production 1 Nothing [Left 'h', Left 'i'])
            let startState = fromJust $ atnProductionStart atn 1
            assertEqual "should have found the correct state" (Just [3]) $ atnFindTransition atn startState (Left 'h')

    ]
