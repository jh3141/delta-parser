{-# LANGUAGE GADTs,StandaloneDeriving,UndecidableInstances,FlexibleContexts,ScopedTypeVariables,TupleSections #-}
module Text.Parser.ALLStar where

import Data.IORef
import Text.Parser.Delta.Classifiable
import Text.Parser.Delta.Util
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

-- | A predicate is a function that examines a parse stack and a "state" (which is a user defined type)
-- and returns a bool.  It is used as a guard to allow productions to be context sensitive.
type Predicate stack state = stack -> state -> Bool

data Symbol t nt s c where
    Terminal ::    (Classifiable c t, Show c, Ord c) =>
                   c                           -> Symbol t nt s c
    NonTerminal :: Classifiable c t =>
                   nt -> [Production t nt s c] -> Symbol t nt s c

deriving instance (Show c, Show nt, Classifiable c t) => Show (Symbol t nt s c)
deriving instance (Eq c, Eq nt, Classifiable c t) =>     Eq (Symbol t nt s c)
deriving instance (Ord c, Ord nt, Classifiable c t) =>   Ord (Symbol t nt s c)

-- | A Production is a rule of a grammar.  There are two subtypes, 'Production' (which represents
-- a translation from a non-terminal to a sequence of terminals and non-terminals) and 'Mutation'
-- (which performs a translation of the parser state).
-- The type of 'Production' has four variables: 't' (the type of terminals), 'nt' (the type of
-- non-terminals), 's' (the type of states) and 'c' (the type of input units, e.g. characters).
-- There must exist a 'Classifiable' class that allows 'c' units to be translated to terminals,
-- and 'c' and 'nt' are both expected to implement the 'Show' and 'Ord' classes.
data Production t nt s c where
    -- | Constructor for production grammar rules.  Accepts an integer production number,
    -- an optional predicate, and a sequence of either characters or non-terminals.
    Production :: (Classifiable c t, Show t, Ord t, Show nt, Ord nt) =>
                  Int -> Maybe (Predicate [nt] s) -> [Either t nt] -> Production t nt s c
    -- | Constructor for mutators.  Accepts an integer production number, and a function that
    -- translates from one state to another.
    Mutation   :: Int -> (s -> s)                                  -> Production t nt s c

-- | Implementation of 'Show' for 'Production's (for the purpose of debugging)
instance Show (Production t nt s c) where
    show (Production n (Just _) syms) = "{pred} " ++ show n ++ ": " ++ unwords (map (either show show) syms)
    show (Production n Nothing syms)  = show n ++ ": " ++ unwords (map (either show show) syms)
    show (Mutation   _ _)             = "{mu}"

-- | Equality testing for 'Production's.
instance Eq (Production t nt s c) where
    (Production n (Just _) syms) == (Production n' (Just _) syms') = n == n' && syms == syms'
    (Production n Nothing  syms) == (Production n' Nothing  syms') = n == n' && syms == syms'
    (Mutation n _)               == (Mutation   n' _)              = n == n' -- mutations are assumed identical if they have the same serial number
    _                            == _                              = False

-- | Ordering of 'Production's.
instance Ord (Production t nt s c) where
    compare (Production n _ _) (Production n' _ _) = compare n n'
    compare (Production _ _ _) _                   = LT
    compare (Mutation   n _)   (Mutation   n' _)   = compare n n'
    compare (Mutation   _ _)   _                   = GT

-- | Represents an edge in an Augmented Transition Network, used to encapsulate
-- the production rules of the grammar in a form that is easy to translate
-- to the deterministic finite state automaton that is used to predict grammar
-- productions when ambiguities arise.  The edges in an ATN are non-deterministic
-- and therefore are not necessarily followed in every situation where they may
-- be followed.  The constructed DFA uses states that are representations of the
-- possible states of the ATN.
data AutomatonEdge t nt s c where
    -- | An Epsilon edge is an edge that can be followed at any time
    Epsilon         ::                              AutomatonEdge t nt s c
    -- | A TerminalEdge is an edge that can be followed if a terminal
    -- symbol of the appropriate class is located in a partially-parsed input
    TerminalEdge    :: (Ord t, Show t)   => t ->    AutomatonEdge t nt s c
    -- | A NonTerminalEdge is an edge that can be followed when a non-terminal
    -- symbol is located in the input
    NonTerminalEdge :: (Ord nt, Show nt) => nt ->   AutomatonEdge t nt s c
    -- | A PredicateEdge is an edge that can be followed when a predicate on
    -- the set of non-terminals to the left of the current parse point
    -- and the current state returns true
    PredicateEdge   :: Int -> Predicate [nt] s ->   AutomatonEdge t nt s c
    -- | A MutationEdge is an edge that can be followed at any time, and which
    -- produces a new state from the current state, which may be used by
    -- any predicates later on in the network.
    MutationEdge    :: Int -> (s -> s)    ->        AutomatonEdge t nt s c

-- | Returns true iff an edge is an 'Epsilon' edge
edgeIsEpsilon :: AutomatonEdge t nt s c -> Bool
edgeIsEpsilon Epsilon = True
edgeIsEpsilon _       = False

-- | Returns true iff an edge is a non-terminal edge
edgeNonTerminal :: AutomatonEdge t nt s c -> Maybe nt
edgeNonTerminal (NonTerminalEdge nt) = Just nt
edgeNonTerminal _                    = Nothing

-- | Returns true iff an edge is a terminal edge
edgeTerminal :: AutomatonEdge t nt s c -> Maybe t
edgeTerminal (TerminalEdge c) = Just c
edgeTerminal _                = Nothing

-- | Returns true iff an edge is a predicate edge
edgePredicate :: AutomatonEdge t nt s c -> Maybe (Int, Predicate [nt] s)
edgePredicate (PredicateEdge n p) = Just (n,p)
edgePredicate _                   = Nothing

-- | Returns true iff an edge is a mutation edge
edgeMutation :: AutomatonEdge t nt s c -> Maybe (Int, s -> s)
edgeMutation (MutationEdge n f) = Just (n,f)
edgeMutation _                  = Nothing

-- | Automaton edges may be examined for equality
instance Eq (AutomatonEdge t nt s c) where
    Epsilon               == Epsilon               = True
    (TerminalEdge c)      == (TerminalEdge c')     = c == c'
    (NonTerminalEdge t)   == (NonTerminalEdge t')  = t == t'
    (PredicateEdge n _)   == (PredicateEdge n' _)  = n == n'
    (MutationEdge n _)    == (MutationEdge n' _)   = n == n'
    _                     == _                     = False

-- | Automaton edges may be ordered (in the order Epsilon, TerminalEdge,
-- NonTerminalEdge, PredicateEdge, MutationEdge)
instance Ord (AutomatonEdge t nt s c) where
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

-- | Automaton edges may be displayed for debugging purposes
instance Show (AutomatonEdge t nt s c) where
    show Epsilon              = "{epsilon}"
    show (TerminalEdge c)     = show c
    show (NonTerminalEdge nt) = "<" ++ show nt ++ ">"
    show (PredicateEdge n _)  = "{predicate " ++ show n ++ "}"
    show (MutationEdge n _)   = "{mutation " ++ show n ++ "}"

-- | represents the augmented transition network form of a grammar
data Classifiable c t => ATN t nt s c = ATN {
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
        atnTransitionMap         :: IntMap (M.Map (AutomatonEdge t nt s c) [Int]),
        -- | for each state that is a final state, identifies the non-terminal that is produced in that state
        atnEndStateNonTerminal   :: IntMap nt
    }
    deriving (Show, Eq)

-- | represents the calculated portions of the (potentially-infinite) deterministic finite state automaton that predicts
-- the production to take at each choice point in the parse.  uses mutable hash tables to allow new states and edges
-- to be added easily.
data Classifiable c t => DFA t nt s c = DFA {
        dfaNextAvailableId :: Int,                                              -- id of next state to add to automaton
        dfaATNStateToDFA :: H.CuckooHashTable (Int,Int) Int,                    -- (production,index) -> state id
        dfaStates        :: H.CuckooHashTable Int (Set (Int,Int), M.Map c Int), -- state id -> (set (production,index), token -> state id)
        dfaAcceptStates  :: IntMap Int                                          -- states that produce a prediction
    }

-- | stores mutable references to a cached ATN and lookahead DFA for a grammar
data Classifiable c t => AutomataCache t nt s c = AutomataCache {
        cachedATN :: IORef (Maybe (ATN t c nt s)),
        cachedLookaheadDFA :: IORef (Maybe (DFA t nt s c))
    } deriving Eq

-- | Automata caches can show whether ATN and DFA fields are populated for debugging purposes
instance Classifiable c t => Show (AutomataCache t nt s c) where
    show acache = "{cache" ++ (if isATNAvailable acache then "-atn" else "") ++
                              (if isDFAAvailable acache then "-dfa" else "") ++ "}"

-- | A Grammar consists of a set of symbols (along with their associated rules),
-- a start symbol, and a cache optionally containing the two automata that are
-- used for parsing it.

data Grammar t nt s c where
    Grammar    :: Classifiable c t => [Symbol t nt s c] -> nt -> AutomataCache t nt s c -> Grammar t nt s c

deriving instance (Show c, Show nt) => Show (Grammar t nt s c)
deriving instance (Eq c, Eq nt, Classifiable c t) => Eq (Grammar t nt s c)

-- | The result of successfully parsing an input stream is a parse tree, showing the productions
-- used during parsing.
data ParseTree t nt s c where
    ParseTree :: Symbol t nt s c -> s -> [Either t (ParseTree t nt s c)] -> s -> ParseTree t nt s c

-- | Combines an ATN with details required for adding information about a
-- production (the state associated with the most recently added node in the
-- production, the end state associated with the non-terminal being produced,
-- and the number of symbols added in the production so far).
type ATNWithProductionCursor t nt s c = (ATN t nt s c, (Int, Int, Int))

-- | Combines an ATN with the start and end state for a non-terminal (it
-- is assumed that the caller knows from context which non-terminal they refer
-- to).
type ATNWithNonTerminalState t nt s c = (ATN t nt s c, (Int, Int))

-- | Returns the start symbol of a Grammar
startSymbol :: Classifiable c t => Grammar t nt s c -> nt
startSymbol (Grammar _ ss _) = ss

-- | Unsafely check if an ATN is available for a grammar. Should only be used for debugging.
isATNAvailable :: Classifiable c t => AutomataCache t nt s c -> Bool
isATNAvailable (AutomataCache hATN _) = unsafePerformIO $ isJust <$> readIORef hATN

-- | Unsafely check if a Lookahead DFA is available for a grammar. Should only be used for debugging.
isDFAAvailable :: Classifiable c t => AutomataCache t nt s c -> Bool
isDFAAvailable (AutomataCache _ hDFA) = unsafePerformIO $ isJust <$> readIORef hDFA

-- | Creates an empty automata cache (containing neither an ATN nor a DFA)
mkCache :: Classifiable c t => IO (AutomataCache t nt s c)
mkCache = AutomataCache <$> newIORef Nothing <*> newIORef Nothing

-- | Creates an empty automata cache for a language with character input and
-- strings for non-terminals (convenience function)
mkCacheCSI :: IO (AutomataCache Char String Int Char)
mkCacheCSI = mkCache

-- | Produces an empty ATN
emptyATN :: Classifiable c t => ATN t nt s c
emptyATN = ATN 0 IM.empty M.empty IM.empty IM.empty IM.empty

-- | Produces an empty ATN for character input with strings for non-terminals
-- and integers for state (convenience function)
emptyATNCSI :: ATN Char String Int Char
emptyATNCSI = emptyATN

-- | Looks up an ATN state and returns the production number that the state was
-- created to represent
atnStateToProduction :: Classifiable c t => ATN t nt s c -> Int -> Maybe Int
atnStateToProduction atn state = fst <$> (IM.lookup state (atnStateProductionIndex atn) >>= maybeFromRight)

-- | Given an 'Either', return a 'Maybe' that contains the 'Right' value of the 'Either' (or 'Nothing' for a 'Left'
-- branch).
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

addProductionToATN :: (Classifiable c t, Show c) => ATN t nt s c -> nt -> Production t nt s c -> ATN t nt s c
addProductionToATN atn nt (Production prodNum optPred symbols) =
    process atn
    where
        process = atnAddOrFindNonTerminal nt >>>
                  atnAddProductionStartState prodNum >>>
                  atnAddProductionPredicate prodNum optPred >>>
                  atnAddProductionSymbols prodNum symbols >>>
                  atnAddEndStateLink
addProductionToATN _ _ (Mutation _ _) = error "adding mutators to ATN not supported"

-- | For a given non-terminal and an ATN, return an ATN (possibly modified by
-- adding index entries and start/accept states for the non-terminal) and a
-- tuple defining the start and accept states for the non-terminal.
atnAddOrFindNonTerminal :: (Ord nt, Classifiable c t) => nt -> ATN t nt s c -> ATNWithNonTerminalState t nt s c
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

-- | Given a production number and an tuple containing an ATN and the start
-- and stop states for a spefic non-terminal (which is assumed to be produced by
-- the identified production), allocate a start state for the production,
-- update indices, add an epsilon transition from the non-terminal start state
-- to the production start state, and return the ATN along with a triple defining
-- the non-terminal start and stop states and the allocated production start state.
atnAddProductionStartState :: (Ord nt, Classifiable c t) => Int -> ATNWithNonTerminalState t nt s c -> ATNWithProductionCursor t nt s c
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

-- | Given a production number and optional predicate on the production, add a
-- predicate edge to
atnAddProductionPredicate :: (Ord nt, Classifiable c t) => Int -> Maybe (Predicate [nt] s) -> ATNWithProductionCursor t nt s c -> ATNWithProductionCursor t nt s c
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

-- | Update an ATN
atnAddProductionSymbols :: (Ord t, Ord nt, Show t, Show c, Show nt, Classifiable c t) => Int -> [Either t nt] -> ATNWithProductionCursor t nt s c -> ATNWithProductionCursor t nt s c
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

-- | Update an ATN to add a transition from the last state in a production to the
-- accept state for the non-terminal produced by the production.
atnAddEndStateLink :: Classifiable c t => ATNWithProductionCursor t nt s c -> ATN t nt s c
atnAddEndStateLink (atn, (ntLast, ntEnd, _)) = atn {
        atnTransitionMap = insertTransition ntLast ntEnd Epsilon $ atnTransitionMap atn
    }


-- | Add a transition to a transition map from 'fromState' to 'toState' with the
-- edge label 'edge'.
insertTransition :: Classifiable c t => Int -> Int -> AutomatonEdge t nt s c -> IntMap (M.Map (AutomatonEdge t nt s c) [Int]) -> IntMap (M.Map (AutomatonEdge t nt s c) [Int])
insertTransition fromState toState edge transitionMap =
    case IM.lookup fromState transitionMap of
        Nothing    -> IM.insert fromState (M.fromList [(edge, [toState])]) transitionMap
        Just edges -> IM.insert fromState (M.insertWith (++) edge [toState] edges) transitionMap

-- | Examine an ATN for potential problems that will prevent it being usefully implemented.
-- Returns a list of messages describing the located problems and the sequence of production numbers involved.
-- The message list is empty if the ATN is well-formed.
-- Currently detects cases where non-terminals are used for transitions but do
-- not have a corresponding accept state (i.e. they are used in the grammar but
-- are not defined), and left-recursive definitions (including definitions that
-- contain a sequence of left derivations that are mutually recursive).
verifyATN :: (Show nt, Ord nt, Classifiable c t) => ATN t nt s c -> [(String, [Int])]
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

-- | Given an ATN and a non-terminal defined within that ATN, find all valid
-- states that can be used to begin parsing at the specified non-terminal.
allProductionStarts :: (Ord nt, Classifiable c t) => ATN t nt s c -> nt -> [Int]
allProductionStarts atn nt =
    case fst <$> M.lookup nt (atnNonTerminalStates atn) of
        Just startState -> followEpsilons atn startState
        Nothing         -> []

-- | Given an ATN and a state in the ATN, find all successor states that can
-- be consumed without consuming input (i.e. by following transitions that are
-- labelled with epsilon).
followEpsilons :: Classifiable c t => ATN t nt s c -> Int -> [Int]
followEpsilons atn s =
    let stateTransitions = IM.lookup s (atnTransitionMap atn)
        maybeOutputStates = stateTransitions >>= M.lookup Epsilon
    in  concat (maybeToList maybeOutputStates)

-- | Find edges from a given ATN state that correspond to non-terminals.
-- Returns a list of (non-terminal, state-after-non-terminal-accepted) pairs.

nonTerminalEdgesFrom :: Classifiable c t => ATN t nt s c -> Int -> [(nt, Int)]
nonTerminalEdgesFrom atn state =
    case IM.lookup state (atnTransitionMap atn) of
        Just stateTransitions -> concatMap expandSelectedEdges (first edgeNonTerminal <$> M.toAscList stateTransitions)
        Nothing               -> []
    where
        expandSelectedEdges (Nothing, _) = []
        expandSelectedEdges (Just nt, states) = [(nt, s) | s <- states]

-- | For a given ATN and a non-terminal root node appearing in that NT, find
-- the shortest left-most derivations from that root node to any sequence of symbols
-- beginning with each reachable initial non-terminal.
--
-- The resulting map of non-terminals to derivations will contain an entry for the
-- given root non-terminal if and only if there is a left-recursive rule that
-- allows derivation of it.  Such a rule is not-permitted in grammars that can
-- be parsed by LL parsers, including ALL(*).
--
-- Derivations are returned in reverse order (i.e. with the most recently applied
-- rule first), as this is easier to calculate.
leftmostNonTerminals :: forall c nt s t . (Ord nt, Classifiable c t) => ATN t nt s c -> nt -> M.Map nt [Int]
leftmostNonTerminals atn root =
    findPathsFrom root [] M.empty
    where
        -- find all shortest derivations that include a given non-terminal as their
        -- leftmost symbol, which is reached by a given prefix list of derivations,
        -- merging into a given map of derivations if and only if they are shorter
        -- than existing derivations in the map.
        findPathsFrom :: nt -> [Int] -> M.Map nt [Int] -> M.Map nt [Int]
        findPathsFrom nt path shortestPaths = mergeNonTerminals shortestPaths path $ allProductionStarts atn nt

        -- merge a map of derivations to given non-terminals with newer
        -- derivations found by considering a given derivation prefix and list
        -- of possible next derivations to add (updating derivations in the map
        -- where this reults in a shorter derivation to the same non-terminal
        -- or adding new derivations when a non-terminal is found for the first time),
        -- recursively expanding each new entry added to the map.
        mergeNonTerminals :: M.Map nt [Int] -> [Int] -> [Int] -> M.Map nt [Int]
        mergeNonTerminals shortestPaths _ [] = shortestPaths
        mergeNonTerminals shortestPaths currentPath (state:states) = foldl' (addShorterPath (state:currentPath))
                                                                            (mergeNonTerminals shortestPaths currentPath states)
                                                                            (nonTerminalEdgesFrom atn state)

        -- given a derivation to a specified leftmost non-terminal and a map of
        -- existing paths, if the path is shorter than any existing path (or if
        -- there are no existing paths) then add the path to the map and
        -- recursively attempt to add paths found that begin with that prefix.
        -- the non-terminal is accepted in the form of a tuple with an additional
        -- integer argument as a convenience (this function is called with the
        -- result of 'nonTerminalEdgesFrom', which returns a list of valid
        -- state transitions; we don't care about the resulting state).
        addShorterPath :: [Int] -> M.Map nt [Int] -> (nt, Int) -> M.Map nt [Int]
        addShorterPath path shortestPaths (nt, _) =
            case M.lookup nt shortestPaths of
                Nothing                                 -> findPathsFrom nt path $ M.insert nt path shortestPaths
                Just existingPath
                    | length existingPath > length path -> findPathsFrom nt path $ M.insert nt path shortestPaths
                    | otherwise                         -> shortestPaths

-- | Find the start state of a given production in an ATN
atnProductionStart :: Classifiable c t => ATN t nt s c -> Int -> Maybe Int
atnProductionStart atn prodnum = IM.lookup prodnum $ atnProductionStartState atn

atnFindTransition :: (Classifiable c t, Ord t, Ord nt, Show t, Show nt) => ATN t nt s c -> Int -> Either c nt -> Maybe [Int]
atnFindTransition atn state inp =
    do
        statemap <- IM.lookup state $ atnTransitionMap atn
        M.lookup (expectedEdge inp) statemap
    where
        expectedEdge (Left term)     = TerminalEdge $ classification term
        expectedEdge (Right nonterm) = NonTerminalEdge nonterm
        
        
-- | Maximum number of symbols in a production, which is used for generating a unique number
-- for each position in a production based on the number of the production.  This may safely
-- be increased as necessary, but doing so may decrease efficiency for grammars with large
-- numbers of productions.  The default value is suitable for most manually produced grammars,
-- but may not be appropriate for complex machine generated grammars.
productionMaxLength :: Int
productionMaxLength = 1000

-- | type of ATN interpreter states
type ATNInterpretationState nt s = S.Set Int

-- | apply a function of individual ATN states to interpreter states
(<++) :: Foldable f => ATNInterpretationState nt s -> (Int -> f Int) -> ATNInterpretationState nt s
st <++ f = foldMapConcat f S.singleton st

-- | find all valid ATN interpreter start states (including following epsilon paths) for a given nonterminal
atnNonterminalStart :: (Classifiable c t, Ord nt) => ATN t nt s c -> nt -> ATNInterpretationState nt s
atnNonterminalStart atn nonterm = S.fromList $ allProductionStarts atn nonterm

-- | find next valid state set given current state and next input symbol
atnStep :: (Classifiable c t, Ord t, Ord nt, Show t, Show nt) => ATN t nt s c -> ATNInterpretationState nt s -> c -> ATNInterpretationState nt s
atnStep atn st c = st <++ (\ s -> fromMaybe [] (atnFindTransition atn s $ Left c))
