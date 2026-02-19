{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module MapLemmas where

import TypeAliases
import Utils
import qualified Data.Set as S
import Language.Haskell.Liquid.ProofCombinators

-- Lemmas specific for the LH-friendly implementation of maps ------------------

#if LiquidOn

import qualified Liquid.Data.Map as M

-- if lookup returns Just, then the key is in the set of keys
{-@ reflect elementLemma @-}
{-@ elementLemma :: key:k -> val:v -> {m:M.Map k v | M.lookup key m == Just val}
                 -> { M.member key m } @-}
elementLemma :: Ord k => k -> v -> M.Map k v -> Proof
elementLemma k v (M.MBin k' _ m) = if k == k' then () else elementLemma k v m

-- a value larger than all set elements will never be returned by lookup
{-@ notElemLemma :: key:k -> n:Int -> m:{M.Map k (Btwn 0 n) | M.member key m}
                 -> { M.lookup' key m /= n } @-}
notElemLemma :: Eq k => k -> Int -> M.Map k Int -> Proof
notElemLemma key n M.MTip = ()
notElemLemma key n (M.MBin k _ m) = if key == k then () else notElemLemma key n m

-- when the key is in the map, safe lookup works as normal lookup
{-@ lookupLemma :: key:k -> m:{M.Map k v | M.member key m}
                -> { M.lookup key m == Just (M.lookup' key m) } @-}
lookupLemma :: Eq k => k -> M.Map k v -> Proof
lookupLemma key (M.MBin k _ m) = if key == k then () else lookupLemma key m

#else

import qualified Data.Map as M

-- they have no computational value, but we do need them to be defined

elementLemma :: k -> v -> M.Map k v -> Proof
elementLemma _ _ _ = ()

notElemLemma :: k -> Int -> M.Map k Int -> Proof
notElemLemma _ _ _ = ()

lookupLemma :: k -> M.Map k v -> Proof
lookupLemma _ _ = ()

#endif
