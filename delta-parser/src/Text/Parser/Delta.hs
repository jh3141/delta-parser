{-# LANGUAGE GADTs, FlexibleContexts #-}
module Text.Parser.Delta where

import Text.Parser.Delta.Classifiable
import Text.Parser.Delta.TokenIndex

-- | The type of a delta parser.
-- Type parameters are:
--   * t: the type of tokens, which are required to be 'Classifiable'
--   * c: the type to which tokens are classified
--   * l: the type produced by the parser to the left of this parser
--   * i: ("index") a type that can be used to associate token categories to values
--   * r: the type of the results produced by the Parser

data DeltaParser t c l i r where
    Parse1 :: (Classifiable t c, TokenIndex i c (l -> t -> r)) => i c (l -> t -> r) -> DeltaParser t c l i r
    ParseChain :: (Classifiable t c, TokenIndex i c (l -> t -> x), TokenIndex i c (x -> t -> r)) =>
                  DeltaParser t c l i x -> DeltaParser t c x i r -> DeltaParser t c l i r

data ParseError c where
    UnexpectedToken :: c -> [(c, Maybe c)] -> ParseError c
    UnexpectedEOF   :: [(c, Maybe c)]      -> ParseError c
    deriving (Eq, Show)

acceptToken :: (Classifiable t c, TokenIndex i c (l -> t -> r)) => c -> (l -> t -> r) -> DeltaParser t c l i r
acceptToken tokenClass handler = Parse1 (addSingleToken emptyTokenIndex tokenClass handler)

runParser :: Classifiable t c => DeltaParser t c l i r -> l -> [t] -> Either (ParseError c) (r,[t])
runParser (Parse1 index) _ [] = Left $ UnexpectedEOF $ validTokenRanges index
runParser (Parse1 index) leftContext (token:tokens) = lookupToken index
    (Left $ UnexpectedToken tokenClass $ validTokenRanges index) -- if not found
    (Right . addTokenTail tokens . applyToken)                   -- if found
    tokenClass                                                   -- what to find
  where
    tokenClass = classification token
    applyToken fn = fn leftContext token
    addTokenTail tokenTail result = (result, tokenTail)

runParser (ParseChain parseL parseR) leftContext tokens =
    case runParser parseL leftContext tokens of
         (Right (resultL, remainingTokensL)) -> runParser parseR resultL remainingTokensL
         (Left err)                          -> Left err
