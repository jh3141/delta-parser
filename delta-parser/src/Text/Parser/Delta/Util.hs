module Text.Parser.Delta.Util where

import Data.Foldable

-- | apply a function to a foldable that returns foldable results, converting each
-- item to a monoid using a given creation function, and combining the results.
-- uses a strict right fold, so the source foldable must be finite.

foldMapConcat :: (Foldable t, Foldable u, Monoid m) => (a -> t b) -> (b -> m) -> u a -> m
foldMapConcat f g s = foldr' (mapConcat f g) mempty s

-- | apply a function to a value that returns a foldable result, convert
-- each item to a monoid using a given creation function, then combining results
-- with a specified seed value.
-- uses a strict right fold, so the returned foldables must be finite.
mapConcat :: (Foldable t, Monoid m) => (a -> t b) -> (b -> m) -> a -> m -> m
mapConcat f g element current = foldr' (mappend . g) current (f element)
        
