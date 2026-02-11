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

-- an index larger than all assigned indices has not been assigned
{-@ freshLemma :: n:Int -> m:M.Map k (Btwn 0 n)
               -> { not (elem' n (M.elems m)) } @-}
freshLemma :: Int -> M.Map k Int -> Proof
freshLemma _  M.MTip        = ()
freshLemma x (M.MBin _ _ m) = freshLemma x m

-- if lookup returns Just, then the key is in the LIST of keys
{-@ elementLemma :: key:k -> val:v -> m:{M.Map k v | M.lookup key m == Just val}
                 -> { elem' key (M.keys m) } @-}
elementLemma :: Eq k => k -> v -> M.Map k v -> Proof
elementLemma k v (M.MBin k' _ m) = if k == k' then () else elementLemma k v m

-- if lookup returns Just, then the key is in the SET of keys
{-@ reflect elemLemmaSet @-}
{-@ elemLemmaSet :: key:k -> val:v -> {m:M.Map k v | M.lookup key m == Just val}
                 -> { S.isSubsetOf (S.singleton key) (M.keysSet m) } @-}
elemLemmaSet :: Ord k => k -> v -> M.Map k v -> Proof
elemLemmaSet k v (M.MBin k' _ m) = if k == k' then () else elemLemmaSet k v m

-- if a value is not in the map, then lookup will never return it
{-@ notElemLemma :: key:k -> val:v -> m:{M.Map k v | elem' key (M.keys m)
                                            && not (elem' val (M.elems m))}
                 -> { M.lookup' key m /= val } @-}
notElemLemma :: Eq k => k -> v -> M.Map k v -> Proof
notElemLemma _   _   M.MTip         = ()
notElemLemma key val (M.MBin k _ m) = if key == k then () else notElemLemma key val m

-- an index larger than all assigned indices will never be returned by lookup
{-@ notElemLemma' :: key:k -> n:Int -> m:{M.Map k (Btwn 0 n) | elem' key (M.keys m)}
                  -> { M.lookup' key m /= n } @-}
notElemLemma' :: Eq k => k -> Int -> M.Map k Int -> Proof
notElemLemma' key n m = freshLemma n m ? notElemLemma key n m

-- when the key is in the map, safe lookup works as normal lookup
{-@ lookupLemma :: key:k -> m:{M.Map k v | elem' key (M.keys m)}
                -> { M.lookup key m == Just (M.lookup' key m) } @-}
lookupLemma :: Eq k => k -> M.Map k v -> Proof
lookupLemma key (M.MBin k _ m) = if key == k then () else lookupLemma key m

-- when the key is in the map, safe lookup works as normal lookup, for sets
{-@ lookupLemmaSet :: key:k -> m:{M.Map k v | M.member key m}
                -> { M.lookup key m == Just (M.lookup' key m) } @-}
lookupLemmaSet :: Eq k => k -> M.Map k v -> Proof
lookupLemmaSet key (M.MBin k _ m) = if key == k then () else lookupLemmaSet key m

#else

import qualified Data.Map as M

-- they have no computational value, but we do need them to be defined

freshLemma :: Int -> M.Map k Int -> Proof
freshLemma _ _ = ()

elementLemma :: k -> v -> M.Map k v -> Proof
elementLemma _ _ _ = ()

elemLemmaSet :: k -> v -> M.Map k v -> Proof
elemLemmaSet _ _ _ = ()

notElemLemma :: k -> v -> M.Map k v -> Proof
notElemLemma _ _ _ = ()

notElemLemma' :: k -> Int -> M.Map k Int -> Proof
notElemLemma' _ _ _ = ()

lookupLemma :: k -> M.Map k v -> Proof
lookupLemma _ _ = ()

lookupLemmaSet :: k -> M.Map k v -> Proof
lookupLemmaSet _ _ = ()

#endif
