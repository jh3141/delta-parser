{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Text.Parser.Delta.TokenIndex where

import qualified Data.Map.Strict as MS

class TokenIndex i c v where
    emptyTokenIndex :: i c v
    addTokenRange :: Enum c => i c v -> c -> c -> v -> i c v
    addSingleToken :: i c v -> c -> v -> i c v
    containsToken :: i c v -> c -> Bool
    lookupToken :: i c v -> a -> (v -> a) -> c -> a
    validTokenRanges :: i c v -> [(c, Maybe c)]

instance Ord t => TokenIndex MS.Map t v where
    emptyTokenIndex = MS.empty
    addTokenRange m t1 t2 v = foldr (\ (t',v') m' -> addSingleToken m' t' v') m $ zip [t1 .. t2] (repeat v)
    addSingleToken m t v = MS.insert t v m
    containsToken = flip MS.member
    lookupToken m ifNP ifP t = maybe ifNP ifP $ MS.lookup t m
    validTokenRanges m = zip (MS.keys m) (repeat Nothing)
    
