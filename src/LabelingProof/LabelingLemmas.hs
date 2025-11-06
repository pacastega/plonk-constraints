{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module LabelingProof.LabelingLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
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
                -> { update m ρ σ e == update m' ρ σ e } @-}
updateLemma :: (Eq p, Fractional p) => Int -> Int
                   -> NameValuation p -> LDSL p Int -> M.Map Int p -> Proof
updateLemma m m' ρ e σ = case e of
  LWIRE {} -> ()
  LVAR {} -> ()
  LCONST {} -> ()

  LDIV e1 e2 _ _ -> updateLemma m m' ρ e1 σ ? case update m ρ σ e1 of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LUN _ e1 _ -> updateLemma m m' ρ e1 σ
  LBIN _ e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ σ e1 of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LEQLC e1 _ _ _ -> updateLemma m m' ρ e1 σ

  LNZERO e1 _ -> updateLemma m m' ρ e1 σ
  LBOOL e1    -> updateLemma m m' ρ e1 σ
  LEQA e1 e2  -> updateLemma m m' ρ e1 σ ? case update m ρ σ e1 of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1


-- Lemmas specific for the LH-friendly implementation of maps ------------------
#if LiquidOn

-- an index larger than all assigned indices has not been assigned
{-@ freshLemma :: n:Int -> m:M.Map k (Btwn 0 n)
               -> { not (elem' n (M.elems m)) } @-}
freshLemma :: Int -> M.Map k Int -> Proof
freshLemma _  M.MTip        = ()
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
notElemLemma _   _   M.MTip         = ()
notElemLemma key val (M.MBin k _ m) = if key == k then () else notElemLemma key val m

{-@ notElemLemma' :: key:k -> n:Int -> m:{M.Map k (Btwn 0 n) | elem' key (M.keys m)}
                  -> { M.lookup' key m /= n } @-}
notElemLemma' :: Eq k => k -> Int -> M.Map k Int -> Proof
notElemLemma' key n m = freshLemma n m ? notElemLemma key n m

{-@ lookupLemma :: key:k -> m:{M.Map k v | elem' key (M.keys m)}
                -> { M.lookup key m == Just (M.lookup' key m) } @-}
lookupLemma :: Eq k => k -> M.Map k v -> Proof
lookupLemma key (M.MBin k _ m) = if key == k then () else lookupLemma key m

#else

-- they have no computational value, but we do need them to be defined

freshLemma :: Int -> M.Map k Int -> Proof
freshLemma _ _ = ()

elementLemma :: Eq k => k -> v -> M.Map k v -> Proof
elementLemma _ _ _ = ()

notElemLemma :: Eq k => k -> v -> M.Map k v -> Proof
notElemLemma _ _ _ = ()

notElemLemma' :: Eq k => k -> Int -> M.Map k Int -> Proof
notElemLemma' _ _ _ = ()

lookupLemma :: Eq k => k -> M.Map k v -> Proof
lookupLemma _ _ = ()

#endif
--------------------------------------------------------------------------------


{-@ label1Inc :: op:UnOp p -> e1:{DSL p | wellTyped (UN op e1)} -> m0:Nat -> λ:LabelEnv p Int
              -> m1:Int -> e1':LDSL p Int -> λ1:{LabelEnv p Int | label' e1 m0 λ = (m1, mkList1 e1', λ1)}
              ->  m:Int ->  e':LDSL p Int -> λ':{LabelEnv p Int | label' (UN op e1) m0 λ = (m, mkList1 e', λ')}
              -> {m >= m1} @-}
label1Inc :: Num p => UnOp p -> DSL p -> Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
label1Inc op _ _ _ _ _ _ _ _ _ = case op of
  BoolToF -> ()
  ISZERO  -> ()
  EQLC _  -> ()
  _       -> ()

{-@ label2Inc :: op:{BinOp p | desugaredBinOp op || op == EQL || op == DIV } -> e1:DSL p -> e2:{DSL p | wellTyped (BIN op e1 e2)} -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
              -> m1:Int -> e1':LDSL p (Btwn 0 m1) -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, mkList1 e1', λ1)}
              -> m2:Int -> e2':LDSL p (Btwn 0 m2) -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, mkList1 e2', λ2)}
              ->  m:Int ->  e':LDSL p Int -> λ':{LabelEnv p Int | label' (BIN op e1 e2) m0 λ = (m, mkList1 e', λ')}
              -> ({m2 >= m1}) @-}
label2Inc :: (Num p, Ord p) => BinOp p -> DSL p -> DSL p -> Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
label2Inc _op e1 e2 m0 λ m1 _e1' λ1 _m2 _e2' _λ2 _m _e' _λ'
  = trivial ? case label' e1 m0 λ  of (m1,_,_) -> m1
            ? case label' e2 m1 λ1 of (m2,_,_) -> m2


-- ∀x ∈ dom(Λ) . ρ(x) = σ(Λ(x))
{-@ type Composable Ρ Λ Σ = var:{String | elem' var (M.keys Λ)}
                         -> {(M.lookup var Ρ = M.lookup (M.lookup' var Λ) Σ)} @-}


{-@ labelProofUn  :: m0:Nat -> m1:{Nat | m1 >= m0} -> m:{Nat | m >= m1}
                  -> p1:ScalarDSL p
                  -> op:{UnOp' p | wellTyped (UN op p1)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> σ:M.Map (Btwn 0 m0) p

                  -> Composable ρ λ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ = (m1, mkList1 p1', λ1)}
                  -> e':{LDSL p (Btwn 0 m) | label' (UN op p1) m0 λ = (m, mkList1 e', λ')}
                  -> σ':{M.Map (Btwn 0 m) p | Just σ' = update m ρ σ e'}
                  -> σ1:{M.Map (Btwn 0 m1) p | Just σ1 = update m ρ σ p1'}

                  -> v:p -> v1:{p | M.lookup (outputWire p1') σ1 == Just v1}

                  -> ({ eval p1 ρ = Just (VF v1) <=> M.lookup (outputWire p1') σ1 = Just v1 })
                  -> Composable ρ λ1 σ1

                  -> ({ eval (UN op p1) ρ = Just (VF v) <=>
                      M.lookup (outputWire e') σ' = Just v },
                    Composable ρ λ' σ') @-}
labelProofUn :: (Fractional p, Eq p, Ord p)
              => Int -> Int -> Int -> DSL p -> UnOp p
              -> NameValuation p
              -> LabelEnv p Int
              -> LabelEnv p Int
              -> M.Map Int p

              -> (String -> Proof)

              -> LabelEnv p Int
              -> LDSL p Int
              -> LDSL p Int
              -> M.Map Int p
              -> M.Map Int p

              -> p -> p
              -> Proof -> (String -> Proof)

              -> (Proof, String -> Proof)
labelProofUn m0 m1 m p1 op ρ λ λ1 σ π λ' p1' e' σ' σ1 v v1 ih1 π1 = case op of
  ADDC k -> ((), \x -> π1 x ? notElemLemma' x (outputWire e') λ1)
  MULC k -> ((), \x -> π1 x ? notElemLemma' x (outputWire e') λ1)

  NOT ->       ((), \x -> π1 x ? notElemLemma' x (outputWire e') λ1)
  UnsafeNOT -> ((), \x -> π1 x ? notElemLemma' x (outputWire e') λ1)


{-@ labelProofBin :: m0:Nat -> m1:{Nat | m1 >= m0} -> m2:{Nat | m2 >= m1} -> m:{Nat | m >= m2}
                  -> p1:ScalarDSL p
                  -> p2:ScalarDSL p
                  -> op:{BinOp' p | wellTyped (BIN op p1 p2)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> λ2:LabelEnv p (Btwn 0 m2)
                  -> σ:M.Map (Btwn 0 m0) p

                  -> Composable ρ λ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ  = (m1, mkList1 p1', λ1)}
                  -> p2':{LDSL p (Btwn 0 m2) | label' p2 m1 λ1 = (m2, mkList1 p2', λ2)}

                  -> e':{LDSL p (Btwn 0 m) | label' (BIN op p1 p2) m0 λ = (m, mkList1 e', λ')}
                  -> σ':{M.Map (Btwn 0 m) p | Just σ' = update m ρ σ e'}
                  -> σ1:{M.Map (Btwn 0 m1) p | Just σ1 = update m ρ σ p1'}
                  -> σ2:{M.Map (Btwn 0 m2) p | Just σ2 = update m ρ σ1 p2'}

                  -> v:p
                  -> v1:{p | M.lookup (outputWire p1') σ1 == Just v1}
                  -> v2:{p | M.lookup (outputWire p2') σ2 == Just v2}

                  -> ({ eval p1 ρ = Just (VF v1) <=> M.lookup (outputWire p1') σ1 = Just v1 })
                  -> Composable ρ λ1 σ1

                  -> ({ eval p2 ρ = Just (VF v2) <=> M.lookup (outputWire p2') σ2 = Just v2 })
                  -> Composable ρ λ2 σ2

                  -> ({ eval (BIN op p1 p2) ρ = Just (VF v) <=>
                      M.lookup (outputWire e') σ' = Just v },
                    Composable ρ λ' σ') @-}
labelProofBin :: (Fractional p, Eq p, Ord p)
              => Int -> Int -> Int -> Int -> DSL p -> DSL p -> BinOp p
              -> NameValuation p
              -> LabelEnv p Int -> LabelEnv p Int -> LabelEnv p Int
              -> M.Map Int p

              -> (String -> Proof)

              -> LabelEnv p Int
              -> LDSL p Int -> LDSL p Int -> LDSL p Int
              -> M.Map Int p -> M.Map Int p -> M.Map Int p

              -> p -> p -> p

              -> Proof -> (String -> Proof)
              -> Proof -> (String -> Proof)

              -> (Proof, String -> Proof)
labelProofBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 v v1 v2 ih1 π1 ih2 π2 = case op of
  ADD           -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  SUB           -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  MUL           -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  LINCOMB k1 k2 -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  AND -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  OR  -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  XOR -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  UnsafeAND -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  UnsafeOR  -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  UnsafeXOR -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
