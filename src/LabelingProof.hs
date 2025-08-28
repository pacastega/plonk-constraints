{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--fast" @-}
{- LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--cores=1" @-}

module LabelingProof where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import Utils
import TypeAliases

import Vec
import DSL
import Label
import WitnessGeneration

import Semantics

import Language.Haskell.Liquid.ProofCombinators
import Data.Maybe (fromJust, isJust)
import GHC.Generics ((:.:)(Comp1))

{-@ assume updateLemma :: m:Nat -> m':{Nat | m' >= m}
                -> ρ:NameValuation p -> e:LDSL p (Btwn 0 m)
                -> σ:M.Map (Btwn 0 m) p
                -> { update m ρ e σ == update m' ρ e σ } @-}
updateLemma :: (Eq p, Fractional p) => Int -> Int
                   -> NameValuation p -> LDSL p Int -> M.Map Int p -> Proof
updateLemma m m' ρ e σ = () {- case e of
  LWIRE {} -> ()
  LVAR {} -> ()
  LCONST {} -> ()

  LADD e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LSUB e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LMUL e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LDIV e1 e2 _ _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LADDC e1 _ _ -> updateLemma m m' ρ e1 σ
  LMULC e1 _ _ -> updateLemma m m' ρ e1 σ
  LLINCOMB _ e1 _ e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LNOT e1 _ -> updateLemma m m' ρ e1 σ
  LAND e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LOR  e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LXOR e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LUnsafeNOT e1 _ -> updateLemma m m' ρ e1 σ
  LUnsafeAND e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LUnsafeOR  e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LUnsafeXOR e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LEQLC e1 _ _ _ -> updateLemma m m' ρ e1 σ
  LNZERO e1 _    -> updateLemma m m' ρ e1 σ

  LNZERO e1 _ -> updateLemma m m' ρ e1 σ
  LBOOL e1    -> updateLemma m m' ρ e1 σ
  LEQA e1 e2  -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
-}


-- ∀x ∈ dom(Λ) . ρ(x) = σ(Λ(x))
{-@ type Composable Ρ Λ Σ = var:{String | elem' var (M.keys Λ)} 
                         -> {(M.lookup var Ρ = M.lookup (M.lookup' var Λ) Σ)} @-}

{- 
-- an index larger than all assigned indices has not been assigned
{-@ assume freshLemma :: n:Int -> m:M.Map k (Btwn 0 n)
               -> { not (elem' n (M.elems m)) } @-}
freshLemma :: Int -> M.Map k Int -> Proof
freshLemma x (M.MTip)       = ()
freshLemma x (M.MBin _ _ m) = freshLemma x m

-- if lookup returns Just, then the key is in the list of keys
{-@ assume elementLemma :: key:k -> val:v -> m:{M.Map k v | M.lookup key m == Just val}
                 -> { elem' key (M.keys m) } @-}
elementLemma :: Eq k => k -> v -> M.Map k v -> Proof
elementLemma k v (M.MBin k' _ m) = () --  if k == k' then () else elementLemma k v m
-}

{- 
-- if a value is not in the map, then lookup will never return it
{-@ assume notElemLemma :: key:k -> val:v -> m:{M.Map k v | elem' key (M.keys m)
                                            && not (elem' val (M.elems m))}
           -> { M.lookup' key m /= val } @-}
      
notElemLemma :: Eq k => k -> v -> M.Map k v -> Proof
notElemLemma key val (M.MTip) = ()
notElemLemma key val (M.MBin k v m) = if key == k then () else notElemLemma key val m
-}


{-@  assume notElemLemma' :: key:k -> n:Int -> m:{M.Map k (Btwn 0 n) | elem' key (M.keys m)}
            -> { M.lookup' key m /= n } @-}
notElemLemma' :: Eq k => k -> Int -> M.Map k Int -> Proof
notElemLemma' key n m = undefined -- freshLemma n m ? notElemLemma key n m

{- 
{-@  lookupLemma :: key:k -> m:{M.Map k v | elem' key (M.keys m)}
           -> { M.lookup key m == Just (M.lookup' key m) } @-}
lookupLemma :: Eq k => k -> M.Map k v -> Proof
lookupLemma key (M.MBin k _ m) = if key == k then () else lookupLemma key m
-}


{-@ labelProof1AddLeft :: m0:Nat -> m:{Nat | m >= m0}
                -> p1:{TypedDSL p | scalar p1}
                -> p2:{TypedDSL p | scalar p2 && wellTyped (ADD p1 p2)}
                -> ρ:NameValuation p
                -> λ:LabelEnv p (Btwn 0 m0)
                -> σ:M.Map (Btwn 0 m0) p

                -> Composable ρ λ σ

                -> λ':LabelEnv p (Btwn 0 m)
                -> e':{LDSL p (Btwn 0 m) | label' (ADD p1 p2) m0 λ = (m, mkList1 e', λ')}
                -> σ':{M.Map (Btwn 0 m) p | Just σ' = update m ρ e' σ}

                -> v:p

                -> {eval (ADD p1 p2) ρ = Just (VF v) <=>
                      M.lookup (outputWire e') σ' = Just v }
                     @-}
labelProof1AddLeft :: (Fractional p, Eq p, Ord p)
            => Int -> Int -> DSL p -> DSL p
            -> NameValuation p
            -> LabelEnv p Int
            -> M.Map Int p

            -> (String -> Proof)

            -> LabelEnv p Int
            -> LDSL p Int
            -> M.Map Int p

            -> p

            -> Proof
labelProof1AddLeft m0 m p1 p2 ρ λ σ π λ' e' σ' v = ih1 ? ih2 ?(
       (eval (ADD p1 p2) ρ == Just (VF v))  
   === (liftA2' add (eval p1 ρ) (eval p2 ρ) == Just (VF v))  
   === (Just (add (VF v1) (VF v2)) == Just (VF v))  
   === (Just (VF (v1 + v2)) == Just (VF v))  
   === ( v1 + v2 == v )
   === (M.lookup (outputWire e') σ' == Just v)
   *** QED )
   where (m1, ps1, λ1) = label' p1 m0 λ
         (m2, ps2, λ2) = label' p2 m1 λ1
         p1' = case ps1 of [x] -> x  
         p2' = case ps2 of [x] -> x 
         σ1  = case (update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ)  of Just s -> s 
         σ2  = case (update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1) of Just s -> s 
         v1  = case (M.lookup (outputWire p1') σ1) of Just s -> s 
         v2  = case (M.lookup (outputWire p2') σ2) of Just s -> s
         (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
         (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2




{-@ labelProof1AddRight :: m0:Nat -> m:{Nat | m >= m0}
                -> p1:{TypedDSL p | scalar p1}
                -> p2:{TypedDSL p | scalar p2 && wellTyped (ADD p1 p2)}
                -> ρ:NameValuation p
                -> λ:LabelEnv p (Btwn 0 m0)
                -> σ:M.Map (Btwn 0 m0) p

                -> Composable ρ λ σ

                -> λ':LabelEnv p (Btwn 0 m)
                -> e':{LDSL p (Btwn 0 m) | label' (ADD p1 p2) m0 λ = (m, mkList1 e', λ')}
                -> σ':{M.Map (Btwn 0 m) p | Just σ' = update m ρ e' σ}

                -> v:p

                -> Composable ρ λ' σ'
                     @-}
labelProof1AddRight :: (Fractional p, Eq p, Ord p)
            => Int -> Int -> DSL p -> DSL p
            -> NameValuation p
            -> LabelEnv p Int
            -> M.Map Int p

            -> (String -> Proof)

            -> LabelEnv p Int
            -> LDSL p Int
            -> M.Map Int p

            -> p

            -> String -> Proof
labelProof1AddRight m0 m p1 p2 ρ λ σ π λ' e' σ' v x = π2 x ? notElemLemma' x (outputWire e') λ2
   where (m1, ps1, λ1) = label' p1 m0 λ
         (m2, ps2, λ2) = label' p2 m1 λ1
         p1' = case ps1 of [x] -> x  
         p2' = case ps2 of [x] -> x 
         σ1  = case (update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ)  of Just s -> s 
         σ2  = case (update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1) of Just s -> s 
         v1  = case (M.lookup (outputWire p1') σ1) of Just s -> s 
         v2  = case (M.lookup (outputWire p2') σ2) of Just s -> s
         (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
         (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2



{- 
    let (m1, ps1, λ1) = label' p1 m0 λ
        (m2, ps2, λ2) = label' p2 m1 λ1
        p1' = case ps1 of [x] -> x  
        p2' = case ps2 of [x] -> x 
        σ1  = case (update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ)  of Just s -> s 
        σ2  = case (update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1) of Just s -> s 
        v1  = case (M.lookup (outputWire p1') σ1) of Just s -> s 
        v2  = case (M.lookup (outputWire p2') σ2) of Just s -> s
        (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
        (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2 ? 
           (
                eval (ADD p1 p2) ρ 
            === liftA2' add (eval p1 ρ) (eval p2 ρ)
            === liftA2' add (Just (VF v1)) (Just (VF v2))
            === Just (add (VF v1) (VF v2))
            *** QED 
           )
         ,
            \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
            -}

-- this corresponds to Lemma 2. from the paper
{-@ assume labelProof1 :: m0:Nat -> m:{Nat | m >= m0}
                -> e:{TypedDSL p | scalar e}
                -> ρ:NameValuation p
                -> λ:LabelEnv p (Btwn 0 m0)
                -> σ:M.Map (Btwn 0 m0) p

                -> Composable ρ λ σ

                -> λ':LabelEnv p (Btwn 0 m)
                -> e':{LDSL p (Btwn 0 m) | label' e m0 λ = (m, mkList1 e', λ')}
                -> σ':{M.Map (Btwn 0 m) p | Just σ' = update m ρ e' σ}

                -> v:p

                -> ({ eval e ρ = Just (VF v) <=>
                      M.lookup (outputWire e') σ' = Just v },
                    Composable ρ λ' σ') @-}
labelProof1 :: (Fractional p, Eq p, Ord p)
            => Int -> Int -> DSL p
            -> NameValuation p
            -> LabelEnv p Int
            -> M.Map Int p

            -> (String -> Proof)

            -> LabelEnv p Int
            -> LDSL p Int
            -> M.Map Int p

            -> p

            -> (Proof, String -> Proof)
labelProof1 m0 m e ρ λ σ π λ' e' σ' v = undefined {- case e of
  VAR s τ -> case M.lookup s λ of
    Nothing -> case τ of
      TF -> (trivial,
             \x -> if x == s
                   then trivial
                   else elem' x (M.keys λ')
                     ?? freshLemma (outputWire e') λ ? π x ? M.lookup' x λ)
      TBool -> (trivial,
               \x -> if x == s
                     then trivial
                     else elem' x (M.keys λ')
                       ?? freshLemma (outputWire e') λ ? π x ? M.lookup' x λ)
    Just j  -> (elementLemma s j λ ? π s ? lookupLemma s λ, \x -> π x)
  CONST _ -> (trivial, \x -> π x ? notElemLemma' x (outputWire e') λ)

  BOOLEAN b -> case b of
    True -> (trivial, \x -> π x ? notElemLemma' x (outputWire e') λ)
    False -> (trivial, \x -> π x ? notElemLemma' x (outputWire e') λ)
  ADD p1 p2 ->
    let (m1, ps1, λ1) = label' p1 m0 λ
        (m2, ps2, λ2) = label' p2 m1 λ1
        p1' = case ps1 of [x] -> x  
        p2' = case ps2 of [x] -> x 
        σ1  = case (update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ)  of Just s -> s 
        σ2  = case (update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1) of Just s -> s 
        v1  = case (M.lookup (outputWire p1') σ1) of Just s -> s 
        v2  = case (M.lookup (outputWire p2') σ2) of Just s -> s
        (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
        (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2 ? 
           (
                eval (ADD p1 p2) ρ 
            === liftA2' add (eval p1 ρ) (eval p2 ρ)
            === liftA2' add (Just (VF v1)) (Just (VF v2))
            === Just (add (VF v1) (VF v2))
            *** QED 
           )
         ,
            \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  SUB p1 p2 ->
    let (m1, ps1, λ1) = label' p1 m0 λ
        (m2, ps2, λ2) = label' p2 m1 λ1
        p1' = case ps1 of [x] -> x  
        p2' = case ps2 of [x] -> x 
        σ1  = case (update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ)  of Just s -> s 
        σ2  = case (update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1) of Just s -> s 
        v1  = case (M.lookup (outputWire p1') σ1) of Just s -> s 
        v2  = case (M.lookup (outputWire p2') σ2) of Just s -> s
        (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
        (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2 ? 
           (
                eval (SUB p1 p2) ρ 
            === liftA2' sub (eval p1 ρ) (eval p2 ρ)
            === liftA2' sub (Just (VF v1)) (Just (VF v2))
            === Just (sub (VF v1) (VF v2))
            *** QED 
           )
         ,
            \x -> π2 x ? notElemLemma' x (outputWire e') λ2) 
  MUL p1 p2 ->
    let (m1, ps1, λ1) = label' p1 m0 λ
        (m2, ps2, λ2) = label' p2 m1 λ1
        p1' = case ps1 of [x] -> x
        p2' = case ps2 of [x] -> x
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
        v1 = case M.lookup (outputWire p1') σ1 of Just s -> s
        v2 = case M.lookup (outputWire p2') σ2 of Just s -> s
        (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
        (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
       in (ih1 ? ih2 ?
           (
                eval (MUL p1 p2) ρ 
            === liftA2' mul (eval p1 ρ) (eval p2 ρ)
            === liftA2' mul (Just (VF v1)) (Just (VF v2))
            === Just (mul (VF v1) (VF v2))
            *** QED 
           ),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  DIV p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        (LDIV _ _ w i) = e'
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
     (Just v1, Just v2) ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
           (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
       in (ih1 ? ih2,
           \x -> let j = M.lookup' x λ2
                 in π2 x
                  ? notElemLemma' x i λ2 ? notElemLemma' x w λ2
                  ? (M.lookup j σ'
                    === M.lookup j (M.insert i (v1/v2) σ2)
                    === M.lookup j σ2))
  ADDC p1 _ ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
     Just v1 ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
       in (ih1, \x -> π1 x ? notElemLemma' x (outputWire e') λ1)
  MULC p1 _ ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
     Just v1 ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
       in (ih1, \x -> π1 x ? notElemLemma' x (outputWire e') λ1) 
  LINCOMB _ p1 _ p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
     (Just v1, Just v2) ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
           (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
       in (ih1 ? ih2,
          \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

  NOT p1 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
     Just v1 ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
       in (ih1, \x -> π1 x ? notElemLemma' x (outputWire e') λ1)
  AND p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
     (Just v1, Just v2) ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
           (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
       in (ih1 ? ih2,
          \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  OR p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
     (Just v1, Just v2) ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
           (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
       in (ih1 ? ih2,
          \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  XOR p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
     (Just v1, Just v2) ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
           (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
       in (ih1 ? ih2,
          \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

  UnsafeNOT p1 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
     Just v1 ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
       in (ih1, \x -> π1 x ? notElemLemma' x (outputWire e') λ1)
  UnsafeAND p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
     (Just v1, Just v2) ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
           (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
       in (ih1 ? ih2,
          \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  UnsafeOR p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
     (Just v1, Just v2) ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
           (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
       in (ih1 ? ih2,
          \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  UnsafeXOR p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
     (Just v1, Just v2) ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
           (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
       in (ih1 ? ih2,
          \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

  ISZERO p1 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (LEQLC _ _ w i) = e'
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
     Just v1 ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1 in
         if v1 == 0
         then (ih1, \x -> let j = M.lookup' x λ1 in π1 x
                    ? notElemLemma' x i λ1 ? notElemLemma' x w λ1
                    ? (M.lookup j σ' === M.lookup j (M.insert w zero σ1)
                                     === M.lookup j σ1))
            ? liquidAssert (σ' == M.insert i one (M.insert w zero σ1))
         else (ih1, \x -> let j = M.lookup' x λ1 in π1 x
                    ? notElemLemma' x i λ1 ? notElemLemma' x w λ1
                    ? (M.lookup j σ' === M.lookup j (M.insert w (1/v1) σ1)
                                     === M.lookup j σ1))
            ? liquidAssert (σ' == M.insert i zero (M.insert w (1/v1) σ1))

  EQL p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        (m3, [sub], λ3) = label' (SUB p1 p2) m0 λ
        (LEQLC _ _ w i) = e'
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
        Just σ3 = update m3 ρ sub σ  ? updateLemma m3 m ρ sub σ
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
     (Just v1, Just v2) ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
           (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
       in if v1 == v2
          then (ih1 ? ih2
                ? liquidAssert (M.lookup (outputWire sub) σ3 == Just (v1 - v2)),
                \x -> let j = M.lookup' x λ2 in π2 x
                ? notElemLemma' x i λ2 ? notElemLemma' x w λ2
                ? (M.lookup j σ' === M.lookup j (M.insert w zero σ3)
                                 === M.lookup j σ3))
               ? liquidAssert (σ' == M.insert i one (M.insert w zero σ3))
          else (ih1 ? ih2
                ? liquidAssert (M.lookup (outputWire sub) σ3 == Just (v1 - v2)),
                \x -> let j = M.lookup' x λ2 in π2 x
                ? notElemLemma' x i λ2 ? notElemLemma' x w λ2
                ? (M.lookup j σ' === M.lookup j (M.insert w (1/(v1-v2)) σ3)
                                 === M.lookup j σ3))
               ? liquidAssert (σ' == M.insert i zero (M.insert w (1/(v1-v2)) σ3))

  EQLC p1 k ->
    let (m1, ps1, λ1) = label' p1 m0 λ
        p1' = case ps1 of [x] -> x
        (LEQLC _ _ w i) = e'
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
     Just v1 ->
       let (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1 in
         if v1 == k
         then (ih1, \x -> let j = M.lookup' x λ1 in π1 x
                    ? notElemLemma' x i λ1 ? notElemLemma' x w λ1
                    ? (M.lookup j σ' === M.lookup j (M.insert w 0 σ1)
                                     === M.lookup j σ1))
              ? liquidAssert (σ' == M.insert i one (M.insert w zero σ1))
         else (ih1, \x -> let j = M.lookup' x λ1 in π1 x
                    ? notElemLemma' x i λ1 ? notElemLemma' x w λ1
                    ? (M.lookup j σ' === M.lookup j (M.insert w (1/(v1-k)) σ1)
                                     === M.lookup j σ1))
              ? liquidAssert (σ' == M.insert i zero (M.insert w (1/(v1-k)) σ1))

  BoolToF p1 ->
    let (m1, ps1, λ1) = label' p1 m0 λ
        p1' = case ps1 of [x] -> x
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
       Just v1 -> labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
       Nothing -> case eval p1 ρ of
         Just (VF v1') -> labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1'
         Nothing -> labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 0
-}

{-
-- This is Theorem 2.
{-@ labelProof :: m':Nat -> m:{Nat | m >= m'}
               -> e:{TypedDSL p | scalar e}
               -> as:Store p
               -> ρ:NameValuation p
               -> λ:LabelEnv p (Btwn 0 m) -> λ':LabelEnv p (Btwn 0 m)
               -> {as':[LDSL p (Btwn 0 m)] |
                       labelStore as 0 M.MTip = (m', as', λ')}
               -> {es':[LDSL p (Btwn 0 m)] |
                       label' e m' λ' = (m, es', λ)}
               -> σ:{VecN p m | σ = witnessGen m as' ρ}
               -> {assertionsHold ρ as <=> semanticsHold m σ as'} @-}
labelProof :: (Fractional p, Eq p) => Int -> Int -> DSL p -> Store p
           -> NameValuation p
           -> LabelEnv p Int -> LabelEnv p Int
           -> [LDSL p Int] -> [LDSL p Int]
           -> Vec p
           -> Proof
labelProof m' m e []     ρ λ λ' as' es' σ = trivial
labelProof m' m e (a:as) ρ λ λ' as' es' σ = case a of
  DEF _ _ _ -> undefined -- dummy
  NZERO p1  -> undefined -- IH missing
  BOOL p1   -> undefined -- IH missing
  EQA p1 p2 -> undefined -- IH missing
-}
