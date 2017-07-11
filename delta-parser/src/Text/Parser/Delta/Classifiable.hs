{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
module Text.Parser.Delta.Classifiable where

-- | Classifiable is a typeclass that allows the parser to identify a *class*
-- for any given value in a type.  All values in that class are expected to be
-- parsed identically: although there may be *semantic* differences between
-- values, there should not be *syntactic* differences between values that
-- have the same classification.  This is useful for simplification of parsers
-- that operate on token streams, i.e. it allows all identifiers to be handled
-- identically, regardless of what the actual identifier is.
--
-- The following identity is required to hold for all t, t':
--   (classification t) == (classification t') && (variance t) == (variance t') => t == t'
--
-- Instances are provided for characters (which are considered to be their own
-- classification) and for tuples of up to 4 entries (where the first item
-- is assumed to identify a class, and the remaining items are additional data)

class Eq c => Classifiable t c | t -> c where
    -- | Identifies the class of a given value
    classification :: t -> c

instance Classifiable Char Char where
    classification = id

instance Eq a => Classifiable (a,b) a where
    classification = fst

instance Eq a => Classifiable (a,b,c) a where
    classification (a,_,_) = a

instance Eq a => Classifiable (a,b,c,d) a where
    classification (a,_,_,_) = a
