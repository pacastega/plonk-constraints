{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module BooleanProof where

import TypeAliases
import Utils
import DSL
import Semantics

import qualified Liquid.Data.Map as M
import qualified Data.Set as S

import MapLemmas

import Language.Haskell.Liquid.ProofCombinators

{-@ booleanProof :: ρ:NameValuation p
                 -> e:BoolDSL p
                 -> {v:DSLValue p | eval e ρ == Just v}
                 -> { v == VF 0 || v == VF 1 } @-}
booleanProof :: (Fractional p, Eq p)
             => NameValuation p -> DSL p -> DSLValue p -> Proof
booleanProof ρ e _ = case eval e ρ of Just _ -> trivial


{-@ type TyEnv' i = M.Map i ScalarTy @-}
type TyEnv' i = M.Map i Ty -- map wire indices to types

{-@ reflect insertIfCompatible @-}
{-@ insertIfCompatible :: key:k -> val:v -> m:M.Map k v
       -> Maybe ({m':M.Map k v | M.keysSet m' = S.union (M.keysSet m)
                                                        (S.singleton key)}) @-}
insertIfCompatible :: (Ord k, Eq v) => k -> v -> M.Map k v -> Maybe (M.Map k v)
insertIfCompatible k v m = case M.lookup k m of
  Nothing -> Just (M.insert k v m) -- if k ∉ m, add it
  Just v' -> if v == v'            -- m[k] == v already, do nothing
                then elementLemma k v m ?? Just m
                else Nothing       -- m[k] is some other value, abort

{-@ lookupInsertIC :: key:k -> val:v -> m:M.Map k v
                   -> m':{M.Map k v | Just m' = insertIfCompatible key val m}
                   -> key':k
                   -> { M.lookup key' m' =
                          if key' == key then Just val else M.lookup key' m } @-}
lookupInsertIC :: (Ord k, Eq v) => k -> v -> M.Map k v -> M.Map k v -> k -> Proof
lookupInsertIC k v m m' k' = case M.lookup k m of
  Nothing -> trivial
  Just v' -> if v' == v then trivial else trivial


{-@ insertICIncr :: key:Int -> val:v -> m:M.Map Int v
                 -> m':{M.Map Int v | Just m' = insertIfCompatible key val m}
                 -> MapGE m' m @-}
insertICIncr :: (Eq v) => Int -> v -> M.Map Int v -> M.Map Int v -> Int -> Proof
insertICIncr k v m m' j = case M.lookup k m of
  Nothing -> lookupLemma j m
  Just v' -> if v' == v then trivial else trivial


{-@ reflect tyEnv' @-}
{-@ tyEnv' :: e:TypedLDSL p i -> Maybe ({γ:TyEnv' i | M.keysSet γ =
                                           S.union (wiresE e) (wWiresE e)}) @-}
tyEnv' :: (Ord i) => LDSL p i -> Maybe (TyEnv' i)
tyEnv' e = tyEnv'_ e M.MTip --FIXME: this should be M.empty instead, but that crashes

{-@ reflect tyEnv'_ @-}
{-@ tyEnv'_ :: e:TypedLDSL p i -> γ:TyEnv' i
            -> Maybe ({γ':TyEnv' i |
                      M.keysSet γ' = S.union (M.keysSet γ)
                                             (S.union (wiresE e) (wWiresE e))}) @-}
tyEnv'_ :: (Ord i) => LDSL p i -> TyEnv' i -> Maybe (TyEnv' i)
tyEnv'_ e γ = case inferType' e of --FIXME: this could be a let binding, but that crashes
  Just τ -> case e of
    LWIRE  _ i -> insertIfCompatible i τ γ
    LVAR _ _ i -> insertIfCompatible i τ γ
    LCONST _ i -> insertIfCompatible i τ γ
    LBOOL  _ i -> insertIfCompatible i τ γ

    LDIV e1 e2 w i -> case tyEnv'_ e1 γ of
      Nothing -> Nothing; Just γ1 -> case tyEnv'_ e2 γ1 of
        Nothing -> Nothing; Just γ2 -> case insertIfCompatible w TF γ2 of
          Nothing -> Nothing; Just γw -> insertIfCompatible i τ γw

    LUN _ e1 i -> case tyEnv'_ e1 γ of
      Nothing -> Nothing; Just γ1 -> insertIfCompatible i τ γ1
    LBIN _ e1 e2 i -> case tyEnv'_ e1 γ of
      Nothing -> Nothing; Just γ1 -> case tyEnv'_ e2 γ1 of
        Nothing -> Nothing; Just γ2 -> insertIfCompatible i τ γ2

    LBoolToF e1 -> tyEnv'_ e1 γ
    LEQLC e1 _ w i -> case tyEnv'_ e1 γ of
      Nothing -> Nothing; Just γ1 -> case insertIfCompatible w TF γ1 of
        Nothing -> Nothing; Just γw -> insertIfCompatible i τ γw

    LNIL _ -> Just γ
    LCONS e1 e2 -> case tyEnv'_ e1 γ of
      Nothing -> Nothing; Just γ1 -> tyEnv'_ e2 γ1


{-@ reflect wfEWire @-}
{-@ wfEWire :: TypedLDSL p i -> Bool @-}
wfEWire :: (Ord i) => LDSL p i -> Bool
wfEWire e = wWiresE e `S.isSubsetOf` wiresE e
         && isJust (tyEnv' e)


{-@ outputWireBool :: e:{LDSL p i | booleanE e}
                   -> γ:TyEnv' i
                   -> γ':{TyEnv' i | Just γ' = tyEnv'_ e γ}
                   -> { M.lookup (outputWire e) γ' = Just TBool } @-}
outputWireBool :: (Ord i) => LDSL p i -> TyEnv' i -> TyEnv' i -> Proof
outputWireBool e γ γ' = case e of
  LWIRE  _ i -> lookupInsertIC i TBool γ γ' i
  LVAR _ _ i -> lookupInsertIC i TBool γ γ' i
  LBOOL  _ i -> lookupInsertIC i TBool γ γ' i

  LUN  _  e1   i -> case tyEnv'_ e1 γ of
    Just γ1 -> lookupInsertIC i TBool γ1 γ' i
  LBIN _ e1 e2 i -> case tyEnv'_ e1 γ of
    Just γ1 -> case tyEnv'_ e2 γ1 of
      Just γ2 -> lookupInsertIC i TBool γ2 γ' i

  LEQLC e1 _ w i -> case tyEnv'_ e1 γ of
    Just γ1 -> case insertIfCompatible w TF γ1 of
      Just γw -> lookupInsertIC i TBool γw γ' i


{-@ booleanProof'' :: m:Nat
                   -> σ:WireValuation p m
                   -> e:{LDSL p (Btwn 0 m) | booleanE e && wfEWire e}
                   -> { coherentE m e σ => boolean (M.lookup' (outputWire e) σ) } @-}
booleanProof'' :: (Fractional p, Eq p)
               => Int -> WireValuation p -> LDSL p Int -> Proof
booleanProof'' m σ e = case tyEnv' e of
  Just γ -> outputWireBool e M.MTip γ ?? booleanProof' m σ e M.MTip γ (outputWire e)


{-@ tyEnv'_incr :: e:TypedLDSL p Int -> γ:TyEnv' Int
                -> γ':{TyEnv' Int | Just γ' = tyEnv'_ e γ}
                -> MapGE γ' γ @-}
tyEnv'_incr :: LDSL p Int -> TyEnv' Int -> TyEnv' Int -> (Int -> Proof)
tyEnv'_incr e γ γ' j = case inferType' e of
  Just τ -> case e of
    LWIRE  _ i -> insertICIncr i τ γ γ' j
    LVAR _ _ i -> insertICIncr i τ γ γ' j
    LCONST _ i -> insertICIncr i τ γ γ' j
    LBOOL  _ i -> insertICIncr i τ γ γ' j

    LDIV e1 e2 w i -> case tyEnv'_ e1 γ of
      Just γ1 -> case tyEnv'_ e2 γ1 of
        Just γ2 -> case insertIfCompatible w TF γ2 of
          Just γw -> tyEnv'_incr e1 γ  γ1 j
                  ?? tyEnv'_incr e2 γ1 γ2 j
                  ?? insertICIncr w TF γ2 γw j
                  ?? insertICIncr i τ  γw γ' j

    LUN _ e1 i -> case tyEnv'_ e1 γ of
      Just γ1 -> tyEnv'_incr e1 γ γ1 j
              ?? insertICIncr i τ γ1 γ' j
    LBIN _ e1 e2 i -> case tyEnv'_ e1 γ of
      Just γ1 -> case tyEnv'_ e2 γ1 of
        Just γ2 -> tyEnv'_incr e1 γ  γ1 j
                ?? tyEnv'_incr e2 γ1 γ2 j
                ?? insertICIncr i τ γ2 γ' j

    LBoolToF e1 -> tyEnv'_incr e1 γ γ' j
    LEQLC e1 _ w i -> case tyEnv'_ e1 γ of
      Just γ1 -> case insertIfCompatible w TF γ1 of
        Just γw -> tyEnv'_incr e1 γ γ1 j
                ?? insertICIncr w TF γ1 γw j
                ?? insertICIncr i τ  γw γ' j

    LNIL _ -> trivial
    LCONS e1 e2 -> case tyEnv'_ e1 γ of
      Just γ1 -> case tyEnv'_ e2 γ1 of
        Just γ2 -> tyEnv'_incr e1 γ  γ1 j
                ?? tyEnv'_incr e2 γ1 γ2 j


{-@ booleanProof' :: m:Nat
                  -> σ:WireValuation p m
                  -> e:TypedLDSL p (Btwn 0 m)
                  -> γ:TyEnv' (Btwn 0 m)
                  -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ e γ}
                  -> j:{Btwn 0 m | S.member j (wiresE e)
                                && M.lookup j γ' = Just TBool}
                  -> { coherentE m e σ => boolean (M.lookup' j σ) } @-}
booleanProof' :: (Fractional p, Eq p)
              => Int -> WireValuation p -> LDSL p Int
              -> TyEnv' Int -> TyEnv' Int -> Int
              -> Proof
booleanProof' m σ e γ γ' j = case inferType' e of
  Just τ -> case e of
    LVAR _ τ i -> lookupInsertIC i τ γ γ' j
    LWIRE _ _ -> error "impossible"
    LCONST _ i -> lookupInsertIC i TF γ γ' j ?? error ""
    LBOOL _ _ -> trivial

    LDIV e1 e2 w i -> case tyEnv'_ e1 γ of
      Just γ1 -> case tyEnv'_ e2 γ1 of
        Just γ2 -> case insertIfCompatible w TF γ2 of
          Just γw -> if j == i
                     then lookupInsertIC i TF γw γ' j ?? error ""
                     else lookupInsertIC i TF γw γ' j
                       ?? lookupInsertIC w TF γ2 γw j
                       ?? lookupLemma j γ2
                       ?? if S.member j (wiresE e2)
                          then booleanProof' m σ e2 γ1 γ2 j
                          else if S.member j (wiresE e1)
                               then tyEnv'_incr e2 γ1 γ2 j
                                 ?? lookupLemma j γ1
                                 ?? booleanProof' m σ e1 γ  γ1 j
                               else tyEnv'_incr e γ γ' j

    LUN _ e1 i -> case tyEnv'_ e1 γ of
      Just γ1 -> if j == i
                 then lookupInsertIC i τ γ1 γ' j
                 else lookupInsertIC i τ γ1 γ' j
                   ?? booleanProof' m σ e1 γ γ1 j

    LBIN _ e1 e2 i -> case tyEnv'_ e1 γ of
      Just γ1 -> case tyEnv'_ e2 γ1 of
        Just γ2 -> if j == i
                   then lookupInsertIC i τ γ2 γ' j
                   else lookupInsertIC i τ γ2 γ' j
                     ?? lookupLemma j γ2
                     ?? if S.member j (wiresE e2)
                        then booleanProof' m σ e2 γ1 γ2 j
                        else if S.member j (wiresE e1)
                             then tyEnv'_incr e2 γ1 γ2 j
                               ?? lookupLemma j γ1
                               ?? booleanProof' m σ e1 γ  γ1 j
                             else tyEnv'_incr e γ γ' j

    LBoolToF e1 -> booleanProof' m σ e1 γ γ' j
    LEQLC e1 _ w i -> case tyEnv'_ e1 γ of
      Just γ1 -> case insertIfCompatible w TF γ1 of
        Just γw -> if j == i
                   then trivial
                   else lookupInsertIC i TBool γw γ' j
                     ?? lookupInsertIC w TF    γ1 γw j
                     ?? lookupLemma j γw
                     ?? lookupLemma j γ1
                     ?? booleanProof' m σ e1 γ γ1 j

    LNIL _ -> trivial
    LCONS e1 e2 -> case tyEnv'_ e1 γ of
       Just γ1 -> if S.member j (wiresE e2)
                  then booleanProof' m σ e2 γ1 γ' j
                  else if S.member j (wiresE e1)
                       then tyEnv'_incr e2 γ1 γ' j
                         ?? lookupLemma j γ'
                         ?? lookupLemma j γ1
                         ?? booleanProof' m σ e1 γ γ1 j
                       else tyEnv'_incr e γ γ' j


-- workarounds to fix "crash: unknown constant"

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
