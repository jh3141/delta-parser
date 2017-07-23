{-# LANGUAGE GADTs,StandaloneDeriving,UndecidableInstances,FlexibleContexts,ScopedTypeVariables,TupleSections #-}
module Text.Parser.ALLStar where

import Data.IORef
import Text.Parser.Delta.Classifiable
import qualified Data.HashTable.IO as H
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import System.IO.Unsafe
import Data.Foldable
import Data.Maybe
import Control.Arrow

type Predicate stack state = stack -> state -> Bool

data Symbol t nt s c where
    Terminal ::    (Classifiable t c, Show c, Ord c) =>
                   c                           -> Symbol t nt s c
    NonTerminal :: Classifiable t c =>
                   nt -> [Production t nt s c] -> Symbol t nt s c

deriving instance (Show c, Show nt, Classifiable t c) => Show (Symbol t nt s c)
deriving instance (Eq c, Eq nt, Classifiable t c) =>     Eq (Symbol t nt s c)
deriving instance (Ord c, Ord nt, Classifiable t c) =>   Ord (Symbol t nt s c)

data Production t nt s c where
    Production :: (Classifiable t c, Show c, Ord c, Show nt, Ord nt) =>
                  Int -> Maybe (Predicate [nt] s) -> [Either c nt] -> Production t nt s c
    Mutation   :: Int -> (s -> s)                                  -> Production t nt s c

instance Show (Production t nt s c) where
    show (Production n (Just _) syms) = "{pred} " ++ show n ++ ": " ++ unwords (map (either show show) syms)
    show (Production n Nothing syms)  = show n ++ ": " ++ unwords (map (either show show) syms)
    show (Mutation   _ _)             = "{mu}"

instance Eq (Production t nt s c) where
    (Production n (Just _) syms) == (Production n' (Just _) syms') = n == n' && syms == syms'
    (Production n Nothing  syms) == (Production n' Nothing  syms') = n == n' && syms == syms'
    (Mutation n _)               == (Mutation   n' _)              = n == n' -- mutations are assumed identical if they have the same serial number
    _                            == _                              = False

instance Ord (Production t nt s c) where
    compare (Production n _ _) (Production n' _ _) = compare n n'
    compare (Production _ _ _) _                   = LT
    compare (Mutation   n _)   (Mutation   n' _)   = compare n n'
    compare (Mutation   _ _)   _                   = GT

data AutomatonEdge c nt s where
    Epsilon         ::                              AutomatonEdge c nt s
    TerminalEdge    :: (Ord c, Show c)   => c ->    AutomatonEdge c nt s
    NonTerminalEdge :: (Ord nt, Show nt) => nt ->   AutomatonEdge c nt s
    PredicateEdge   :: Int -> Predicate [nt] s ->   AutomatonEdge c nt s
    MutationEdge    :: Int -> (s -> s)    ->        AutomatonEdge c nt s

edgeIsEpsilon :: AutomatonEdge c nt s -> Bool
edgeIsEpsilon Epsilon = True
edgeIsEpsilon _       = False

edgeNonTerminal :: AutomatonEdge c nt s -> Maybe nt
edgeNonTerminal (NonTerminalEdge nt) = Just nt
edgeNonTerminal _                    = Nothing

edgeTerminal :: AutomatonEdge c nt s -> Maybe c
edgeTerminal (TerminalEdge c) = Just c
edgeTerminal _                = Nothing

edgePredicate :: AutomatonEdge c nt s -> Maybe (Int, Predicate [nt] s)
edgePredicate (PredicateEdge n p) = Just (n,p)
edgePredicate _                   = Nothing

edgeMutation :: AutomatonEdge c nt s -> Maybe (Int, s -> s)
edgeMutation (MutationEdge n f) = Just (n,f)
edgeMutation _                  = Nothing

instance Eq (AutomatonEdge c nt s) where
    Epsilon               == Epsilon               = True
    (TerminalEdge c)      == (TerminalEdge c')     = c == c'
    (NonTerminalEdge t)   == (NonTerminalEdge t')  = t == t'
    (PredicateEdge n _)   == (PredicateEdge n' _)  = n == n'
    (MutationEdge n _)    == (MutationEdge n' _)   = n == n'
    _                     == _                     = False

instance Ord (AutomatonEdge c nt s) where
    compare Epsilon             Epsilon              = EQ
    compare Epsilon             _                    = LT

    compare (TerminalEdge _)    Epsilon              = GT
    compare (TerminalEdge c)    (TerminalEdge c')    = compare c c'
    compare (TerminalEdge _)    _                    = LT

    compare (NonTerminalEdge _) Epsilon              = GT
    compare (NonTerminalEdge _) (TerminalEdge _)     = GT
    compare (NonTerminalEdge n) (NonTerminalEdge n') = compare n n'
    compare (NonTerminalEdge _) _                    = LT

    compare (PredicateEdge _ _) Epsilon              = GT
    compare (PredicateEdge _ _) (TerminalEdge _)     = GT
    compare (PredicateEdge _ _) (NonTerminalEdge _)  = GT
    compare (PredicateEdge n _) (PredicateEdge n' _) = compare n n'
    compare (PredicateEdge _ _) _                    = LT

    compare (MutationEdge n _)  (MutationEdge n' _)  = compare n n'
    compare (MutationEdge _ _)  _                    = GT

instance Show (AutomatonEdge c nt s) where
    show Epsilon              = "{epsilon}"
    show (TerminalEdge c)     = show c
    show (NonTerminalEdge nt) = "<" ++ show nt ++ ">"
    show (PredicateEdge n _)  = "{predicate " ++ show n ++ "}"
    show (MutationEdge n _)   = "{mutation " ++ show n ++ "}"

-- | represents the augmented transition network form of a grammar
data ATN c nt s = ATN {
        -- | number of states in this ATN
        atnStateCount            :: Int,
        -- | for each state, identifies either:
        --
        -- * (in left branch:) a pair containing the non-terminal for which this is the start or end state and either
        --                     True if it is the end state or False if it is the state state, or
        --
        -- * (in the right branch:) the production number that it comes from and the index in that production
        atnStateProductionIndex  :: IntMap (Either (nt,Bool) (Int,Int)),
        -- | identifies the state for which each non-terminal starts and ends
        atnNonTerminalStates     :: M.Map nt (Int,Int),
        -- | identifies the first state of each production
        atnProductionStartState  :: IntMap Int,
        -- | identifies the list of available transitions with any given edge label from each state
        atnTransitionMap         :: IntMap (M.Map (AutomatonEdge c nt s) [Int]),
        -- | for each state that is a final state, identifies the non-terminal that is produced in that state
        atnEndStateNonTerminal   :: IntMap nt
    }
    deriving (Show)

-- | represents the calculated portions of the (potentially-infinite) deterministic finite state automaton that predicts
-- the production to take at each choice point in the parse.  uses mutable hash tables to allow new states and edges
-- to be added easily.
data DFA c nt s = DFA {
        dfaNextAvailableId :: Int,                                              -- id of next state to add to automaton
        dfaATNStateToDFA :: H.CuckooHashTable (Int,Int) Int,                    -- (production,index) -> state id
        dfaStates        :: H.CuckooHashTable Int (Set (Int,Int), M.Map c Int), -- state id -> (set (production,index), token -> state id)
        dfaAcceptStates  :: IntMap Int                                          -- states that produce a prediction
    }

data AutomataCache c nt s = AutomataCache {
        cachedATN :: IORef (Maybe (ATN c nt s)),
        cachedLookaheadDFA :: IORef (Maybe (DFA c nt s))
    } deriving Eq

instance Show (AutomataCache c nt s) where
    show acache = "{cache" ++ (if isATNAvailable acache then "-atn" else "") ++
                              (if isDFAAvailable acache then "-dfa" else "") ++ "}"


data Grammar t nt s c where
    Grammar    :: [Symbol t nt s c] -> nt -> AutomataCache c nt s -> Grammar t nt s c
    deriving (Show, Eq)

data ParseTree t nt s c where
    ParseTree :: Symbol t nt s c -> s -> [Either t (ParseTree t nt s c)] -> s -> ParseTree t nt s c

startSymbol :: Grammar t nt s c -> nt
startSymbol (Grammar _ ss _) = ss

-- | Unsafely check if an ATN is available for a grammar. Should only be used for debugging.
isATNAvailable :: AutomataCache c nt s -> Bool
isATNAvailable (AutomataCache hATN _) = unsafePerformIO $ isJust <$> readIORef hATN

-- | Unsafely check if a Lookahead DFA is available for a grammar. Should only be used for debugging.
isDFAAvailable :: AutomataCache c nt s -> Bool
isDFAAvailable (AutomataCache _ hDFA) = unsafePerformIO $ isJust <$> readIORef hDFA

mkCache :: IO (AutomataCache c nt s)
mkCache = AutomataCache <$> newIORef Nothing <*> newIORef Nothing

emptyATN :: ATN c nt s
emptyATN = ATN 0 IM.empty M.empty IM.empty IM.empty IM.empty

atnStateToProduction :: ATN c nt s -> Int -> Maybe Int
atnStateToProduction atn state = fst <$> (IM.lookup state (atnStateProductionIndex atn) >>= maybeFromRight)

maybeFromRight :: Either a b -> Maybe b
maybeFromRight = either (const Nothing) Just

-- | Build an ATN incrementally by adding one production at a time.
-- Example:
--
-- > addProductionToATN emptyATN "hello" (Production 1 (Just $ \ ss s -> True) [
-- >    Left 'h', Left 'e', Left 'l', Left 'l', Left 'o',
-- >    Right "opt-ws", Right "target-signifier"] :: Production Char String () Char)
--
-- Gives the following transition network:
-- >ATN {
-- >  atnStateCount = 11,
-- >  atnStateProductionIndex = fromList [
-- >    (0,Left ("hello",False)),  -- state 0 is the start state for the "hello" non-terminal
-- >    (1,Left ("hello",True)),   -- state 1 is the accept state for the "hello" NonTerminal
-- >    -- states 2 to 10 are the intermediate states for production 1:
-- >    (2,Right (1,0)), (3,Right (1,1)), (4,Right (1,2)), (5,Right (1,3)),
-- >    (6,Right (1,4)), (7,Right (1,5)), (8,Right (1,6)), (9,Right (1,7)),
-- >    (10,Right (1,8))],
-- >  atnNonTerminalStates = fromList [("hello",(0,1))],  -- locates the start and accept states for "hello"
-- >  atnProductionStartState = fromList [(1,2)],         -- locate the start point of each specific production
-- >  atnTransitionMap = fromList [
-- >     (0,fromList [({epsilon},[2])]),
-- >     (2,fromList [({predicate 1000},[3])]),
-- >     (3,fromList [('h',[4])]),
-- >     ...
-- >     (8,fromList [(<"opt-ws">,[9])]),
-- >     (9,fromList [(<"target-signifier">,[10])]),
-- >     (10,fromList [({epsilon},[1])])],
-- >  atnEndStateNonTerminal = fromList [(1,"hello")]
-- >}
--
-- Note that this network doesn't represent a complete grammar, as it doesn't include start or accept states
-- for the non-terminals "opt-ws" and "target-signifier" that have been referenced in the transition map.
-- 'verifyATN' can be used to check for this condition, as well as other problematic conditions (e.g.
-- left recursion).

addProductionToATN :: ATN c nt s -> nt -> Production t nt s c -> ATN c nt s
addProductionToATN atn nt (Production prodNum optPred symbols) =
    process atn
    where
        process = atnAddOrFindNonTerminal nt >>>
                  atnAddProductionStartState prodNum >>>
                  atnAddProductionPredicate prodNum optPred >>>
                  atnAddProductionSymbols prodNum symbols >>>
                  atnAddEndStateLink

atnAddOrFindNonTerminal :: Ord nt => nt -> ATN c nt s -> (ATN c nt s, (Int, Int))
atnAddOrFindNonTerminal nt atn =
    case M.lookup nt (atnNonTerminalStates atn) of
        Just states -> (atn, states)
        Nothing     ->
            let stateStart = atnStateCount atn
                stateStop  = stateStart + 1
                stateNext  = stateStop + 1
                newStates  = (stateStart, stateStop)
            in (atn {
                    atnStateCount = stateNext,
                    atnStateProductionIndex =
                        IM.insert stateStart (Left (nt, False)) $
                        IM.insert stateStop  (Left (nt, True))  $ atnStateProductionIndex atn,
                    atnNonTerminalStates =
                        M.insert nt newStates (atnNonTerminalStates atn),
                    atnEndStateNonTerminal =
                        IM.insert stateStop nt (atnEndStateNonTerminal atn)
                }, newStates)

atnAddProductionStartState :: Ord nt => Int -> (ATN c nt s, (Int, Int)) -> (ATN c nt s, (Int, Int, Int))
atnAddProductionStartState prodNum (atn,(ntStart,ntEnd)) =
    let
        newState = atnStateCount atn
    in (atn {
        atnStateCount = newState + 1,
        atnStateProductionIndex =
            IM.insert newState (Right (prodNum, 0)) $ atnStateProductionIndex atn,
        atnProductionStartState =
            IM.insert prodNum newState $ atnProductionStartState atn,
        atnTransitionMap = insertTransition ntStart newState Epsilon $ atnTransitionMap atn
    }, (newState, ntEnd, 0))

atnAddProductionPredicate :: Ord nt => Int -> Maybe (Predicate [nt] s) -> (ATN c nt s, (Int, Int, Int)) -> (ATN c nt s, (Int, Int, Int))
atnAddProductionPredicate _ Nothing atn = atn
atnAddProductionPredicate prodNum (Just predicate) (atn,(ntStart,ntEnd,i)) =
    let
        newState = atnStateCount atn
    in (atn {
        atnStateCount = newState + 1,
        atnStateProductionIndex =
            IM.insert newState (Right (prodNum, i+1)) $ atnStateProductionIndex atn,
        atnTransitionMap = insertTransition ntStart newState (PredicateEdge (prodNum * productionMaxLength + i) predicate) $ atnTransitionMap atn
    }, (newState, ntEnd, i+1))

atnAddProductionSymbols :: (Ord c, Ord nt, Show c, Show nt) => Int -> [Either c nt] -> (ATN c nt s, (Int, Int, Int)) -> (ATN c nt s, (Int, Int, Int))
atnAddProductionSymbols _ [] atn = atn
atnAddProductionSymbols prodNum (Left c:syms) (atn,(ntStart,ntEnd,i)) =
    let
        newState = atnStateCount atn
    in atnAddProductionSymbols prodNum syms (atn {
        atnStateCount = newState + 1,
        atnStateProductionIndex =
            IM.insert newState (Right (prodNum, i+1)) $ atnStateProductionIndex atn,
        atnTransitionMap = insertTransition ntStart newState (TerminalEdge c) $ atnTransitionMap atn
    }, (newState, ntEnd, i+1))
atnAddProductionSymbols prodNum (Right nt:syms) (atn,(ntStart,ntEnd,i)) =
    let
        newState = atnStateCount atn
    in atnAddProductionSymbols prodNum syms (atn {
        atnStateCount = newState + 1,
        atnStateProductionIndex =
            IM.insert newState (Right (prodNum, i+1)) $ atnStateProductionIndex atn,
        atnTransitionMap = insertTransition ntStart newState (NonTerminalEdge nt) $ atnTransitionMap atn
    }, (newState, ntEnd, i+1))

atnAddEndStateLink :: (ATN c nt s, (Int, Int, Int)) -> ATN c nt s
atnAddEndStateLink (atn, (ntLast, ntEnd, _)) = atn {
        atnTransitionMap = insertTransition ntLast ntEnd Epsilon $ atnTransitionMap atn
    }


insertTransition :: Int -> Int -> AutomatonEdge c nt s -> IntMap (M.Map (AutomatonEdge c nt s) [Int]) -> IntMap (M.Map (AutomatonEdge c nt s) [Int])
insertTransition fromState toState edge transitionMap =
    case IM.lookup fromState transitionMap of
        Nothing    -> IM.insert fromState (M.fromList [(edge, [toState])]) transitionMap
        Just edges -> IM.insert fromState (M.insertWith (++) edge [toState] edges) transitionMap

-- | Examine an ATN for potential problems that will prevent it being usefully implemented.
-- Returns a list of messages describing the located problems and the sequence of production numbers involved.
-- The message list is empty if the ATN is well-formed.
verifyATN :: (Show nt, Ord nt) => ATN c nt s -> [(String, [Int])]
verifyATN atn = missingNonTerminals ++ leftRecursiveEntries
    where
        missingNonTerminals = concatMap checkForDefinition findUsedNonTerminals
        checkForDefinition (nt, prodNum)
            | M.member nt (atnNonTerminalStates atn) = []
            | otherwise                              = [("Non-terminal symbol " ++ show nt ++ " undefined", prodNum)]
        findUsedNonTerminals = IM.foldMapWithKey collectNonTerminals (atnTransitionMap atn)
        collectNonTerminals state transitions = (,maybeToList $ atnStateToProduction atn state) `S.map` S.fromList (catMaybes $ edgeNonTerminal <$> M.keys transitions)
        leftRecursiveEntries = concat (checkLeftRecursive <$> definedNonTerminals)
        definedNonTerminals = M.keys $ atnNonTerminalStates atn
        checkLeftRecursive nt =
            case M.lookup nt $ leftmostNonTerminals atn nt of
                Just path -> [("Left-recursive definition of non-terminal symbol " ++ show nt, path)]
                Nothing   -> []

allProductionStarts :: Ord nt => ATN c nt s -> nt -> [Int]
allProductionStarts atn nt =
    case fst <$> M.lookup nt (atnNonTerminalStates atn) of
        Just startState -> followEpsilons atn startState
        Nothing         -> []

followEpsilons :: ATN c nt s -> Int -> [Int]
followEpsilons atn s =
    let stateTransitions = IM.lookup s (atnTransitionMap atn)
        maybeOutputStates = stateTransitions >>= M.lookup Epsilon
    in  concat (maybeToList maybeOutputStates)

nonTerminalEdgesFrom :: ATN c nt s -> Int -> [(nt, Int)]
nonTerminalEdgesFrom atn state =
    case IM.lookup state (atnTransitionMap atn) of
        Just stateTransitions -> concatMap expandSelectedEdges (first edgeNonTerminal <$> M.toAscList stateTransitions)
        Nothing               -> []
    where
        expandSelectedEdges (Nothing, _) = []
        expandSelectedEdges (Just nt, states) = [(nt, s) | s <- states]

leftmostNonTerminals :: forall c nt s . Ord nt => ATN c nt s -> nt -> M.Map nt [Int]
leftmostNonTerminals atn root =
    findPathsFrom root [] M.empty
    where
        findPathsFrom :: nt -> [Int] -> M.Map nt [Int] -> M.Map nt [Int]
        findPathsFrom nt path shortestPaths = mergeNonTerminals shortestPaths path $ allProductionStarts atn nt

        mergeNonTerminals :: M.Map nt [Int] -> [Int] -> [Int] -> M.Map nt [Int]
        mergeNonTerminals shortestPaths _ [] = shortestPaths
        mergeNonTerminals shortestPaths currentPath (state:states) = foldl' (addShorterPath (state:currentPath))
                                                                            (mergeNonTerminals shortestPaths currentPath states)
                                                                            (nonTerminalEdgesFrom atn state)

        addShorterPath :: [Int] -> M.Map nt [Int] -> (nt, Int) -> M.Map nt [Int]
        addShorterPath path shortestPaths (nt, _) =
            case M.lookup nt shortestPaths of
                Nothing                                 -> findPathsFrom nt path $ M.insert nt path shortestPaths
                Just existingPath
                    | length existingPath > length path -> findPathsFrom nt path $ M.insert nt path shortestPaths
                    | otherwise                         -> shortestPaths


productionMaxLength :: Int
productionMaxLength = 1000
