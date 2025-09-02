{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module LabelingLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import Utils
import TypeAliases

import DSL
import Label
import WitnessGeneration
import Semantics

import Language.Haskell.Liquid.ProofCombinators

{-@ updateLemma :: m:Nat -> m':{Nat | m' >= m}
                -> ρ:NameValuation p -> e:LDSL p (Btwn 0 m)
                -> σ:M.Map (Btwn 0 m) p
                -> { update m ρ e σ == update m' ρ e σ } @-}
updateLemma :: (Eq p, Fractional p) => Int -> Int
                   -> NameValuation p -> LDSL p Int -> M.Map Int p -> Proof
updateLemma m m' ρ e σ = case e of
  LWIRE {} -> ()
  LVAR {} -> ()
  LCONST {} -> ()

  LDIV e1 e2 _ _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LUN _ e1 _ -> updateLemma m m' ρ e1 σ
  LBIN _ e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LEQLC e1 _ _ _ -> updateLemma m m' ρ e1 σ

  LNZERO e1 _ -> updateLemma m m' ρ e1 σ
  LBOOL e1    -> updateLemma m m' ρ e1 σ
  LEQA e1 e2  -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1


-- an index larger than all assigned indices has not been assigned
{-@ freshLemma :: n:Int -> m:M.Map k (Btwn 0 n)
               -> { not (elem' n (M.elems m)) } @-}
freshLemma :: Int -> M.Map k Int -> Proof
freshLemma x (M.MTip)       = ()
freshLemma x (M.MBin _ _ m) = freshLemma x m

-- if lookup returns Just, then the key is in the list of keys
{-@ elementLemma :: key:k -> val:v -> m:{M.Map k v | M.lookup key m == Just val}
                 -> { elem' key (M.keys m) } @-}
elementLemma :: Eq k => k -> v -> M.Map k v -> Proof
elementLemma k v (M.MBin k' _ m) = if k == k' then () else elementLemma k v m

-- if a value is not in the map, then lookup will never return it
{-@ notElemLemma :: key:k -> val:v -> m:{M.Map k v | elem' key (M.keys m)
                                            && not (elem' val (M.elems m))}
           -> { M.lookup' key m /= val } @-}
notElemLemma :: Eq k => k -> v -> M.Map k v -> Proof
notElemLemma key val (M.MTip) = ()
notElemLemma key val (M.MBin k v m) = if key == k then () else notElemLemma key val m


{-@ notElemLemma' :: key:k -> n:Int -> m:{M.Map k (Btwn 0 n) | elem' key (M.keys m)}
            -> { M.lookup' key m /= n } @-}
notElemLemma' :: Eq k => k -> Int -> M.Map k Int -> Proof
notElemLemma' key n m = freshLemma n m ? notElemLemma key n m

{-@ lookupLemma :: key:k -> m:{M.Map k v | elem' key (M.keys m)}
           -> { M.lookup key m == Just (M.lookup' key m) } @-}
lookupLemma :: Eq k => k -> M.Map k v -> Proof
lookupLemma key (M.MBin k _ m) = if key == k then () else lookupLemma key m
