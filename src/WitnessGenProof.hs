{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof where

import Constraints
import TypeAliases
import DSL
import Semantics
import WitnessGeneration

import Utils

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import Language.Haskell.Liquid.ProofCombinators


{-@ assume myAssume :: a -> {False} @-}
myAssume :: a -> Proof
myAssume _ = ()


{-@ type MapGE M2 M1 = k:{Int | M.member k M1
                             && S.isSubsetOf (M.keySet M1) (M.keySet M2)}
                    -> { M.lookup' k M1 = M.lookup' k M2 } @-}


-- Witness generation never "updates" old keys, only adds new ones.
-- We can think of this as "witnessGenE'(σ,e) ≥ σ".
{-@ wgIncr :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
           -> {e:LDSL p (Btwn 0 m) | wfE e && freshE e σ}
           -> {σ':WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
           -> MapGE σ' σ @-}
wgIncr :: (Eq p, Fractional p) => Int -> NameValuation p -> WireValuation p
       -> LDSL p Int -> WireValuation p -> (Int -> Proof)
wgIncr m ρ σ e σ' j = case e of
  LWIRE  τ i -> trivial ? witnessGenE' m ρ σ e
  LVAR s τ i -> case τ of
    TF -> trivial
    TBool -> trivial
  LCONST x i -> trivial
  LDIV e1 e2 w i -> wgIncr m ρ σ  e1 σ1 j ? wgIncr m ρ σ1 e2 σ2 j
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s
  LUN op e1 i -> wgIncr m ρ σ  e1 σ1 j
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
  LBIN op e1 e2 i -> wgIncr m ρ σ  e1 σ1 j ? wgIncr m ρ σ1 e2 σ2 j
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s
  LEQLC e1 k w i -> wgIncr m ρ σ  e1 σ1 j
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s


{-@ coherentEIncr :: m:Nat -> e:LDSL p (Btwn 0 m)
                  -> {σ1:WireValuation p m | closedExpr m σ1 e && coherentE m e σ1}
                  -> {σ2:WireValuation p m | S.isSubsetOf (M.keySet σ1) (M.keySet σ2)}
                  -> MapGE σ2 σ1
                  -> { coherentE m e σ2 } @-}
coherentEIncr :: (Eq p, Fractional p) => Int -> LDSL p Int -> WireValuation p
              -> WireValuation p -> (Int -> Proof) -> Proof
coherentEIncr m e σ1 σ2 π = case e of
  LWIRE  _ i -> trivial
  LVAR _ τ i -> case τ of
    TF -> trivial
    TBool -> π i
  LCONST _ i -> π i

  LDIV e1 e2  w i -> coherentEIncr m e1 σ1 σ2 π ? coherentEIncr m e2 σ1 σ2 π
                   ? π (outputWire e1) ? π (outputWire e2) ? π i ? π w
  LUN  op e1    i -> coherentEIncr m e1 σ1 σ2 π ? π (outputWire e1) ? π i
  LBIN op e1 e2 i -> coherentEIncr m e1 σ1 σ2 π ? coherentEIncr m e2 σ1 σ2 π
                   ? π (outputWire e1) ? π (outputWire e2) ? π i
  LEQLC e1 k w i -> coherentEIncr m e1 σ1 σ2 π ? π (outputWire e1) ? π i ? π w


{-@ wgSoundE' :: m:Nat
              -> ρ:NameValuation p
              -> σ:WireValuation p m
              -> {e:LDSL p (Btwn 0 m) | wfE e && freshE e σ}
              -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
              -> { coherentE m e σ' } @-}
wgSoundE' :: (Eq p, Fractional p)
          => Int -> NameValuation p -> WireValuation p -> LDSL p Int
          -> WireValuation p -> Proof
wgSoundE' m ρ σ e σ' = case e of
  LWIRE τ i -> trivial
  LVAR s τ i -> case τ of
    TF -> trivial
    TBool -> trivial
  LCONST x i -> trivial

  LDIV e1 e2 w i -> wgSoundE' m ρ σ e1 σ1       -- σ1 ⊢ e1 (by IH)
                  ? coherentEIncr m e1 σ1 σ2 π1 -- σ2 ⊢ e1 (since σ2 ≥ σ1)
                  ? coherentEIncr m e1 σ2 σ' π2 -- σ' ⊢ e1 (since σ' ≥ σ2)

                  ? wgSoundE' m ρ σ1 e2 σ2      -- σ2 ⊢ e2 (by IH)
                  ? coherentEIncr m e2 σ2 σ' π2 -- σ' ⊢ e2 (since σ' ≥ σ2)

                  ? π1 (outputWire e1) -- σ2[i1] == σ1[i1] (since σ2 ≥ σ1)
                  ? π2 (outputWire e1) -- σ'[i1] == σ1[i1] (since σ' ≥ σ2)
                  ? π2 (outputWire e2) -- σ'[i2] == σ2[i2] (since σ' ≥ σ2)

                  -- ? liquidAssert (v1 == M.lookup' (outputWire e1) σ')
                  -- ? liquidAssert (v2 == M.lookup' (outputWire e2) σ')

                  ? liquidAssert (vi == v1 / v2) -- true
                  ? liquidAssert (vw == 1 / v2)  -- true
                  ? liquidAssert (vw * v2 == 1)  -- x/y * y /= x (in ℕ)
                  ? liquidAssert (vi == v1 / v2) -- x/y * y /= x (in ℕ)
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s

          v1 = M.lookup' (outputWire e1) σ1
          v2 = M.lookup' (outputWire e2) σ2
          vw = M.lookup' w σ'
          vi = M.lookup' i σ'

          {-@ π1 :: MapGE σ2 σ1 @-}
          π1 :: Int -> Proof
          π1 j = wgIncr m ρ σ1 e2 σ2 j

          {-@ π2 :: MapGE σ' σ2 @-}
          π2 :: Int -> Proof
          π2 j = trivial ? M.member j σ2 ? M.lookup' j σ'
               ? liquidAssert (j /= i && j /= w)


  LUN op e1 i -> case op of
    ADDC k -> proof; MULC k -> proof; UnsafeNOT -> proof;
    NOT -> myAssume ();
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
          proof = wgSoundE' m ρ σ e1 σ1
                ? coherentEIncr m e1 σ1 σ' (\j -> trivial ? M.member j σ1
                                                          ? M.lookup' j σ')
                ? liquidAssert (v1 == M.lookup' (outputWire e1) σ')
          v1 = M.lookup' (outputWire e1) σ1

  LBIN op e1 e2 i -> case op of
    ADD -> proof; SUB -> proof; MUL -> proof; LINCOMB _ _ -> proof;
    AND -> myAssume (); UnsafeAND -> proof;
    OR  -> myAssume (); UnsafeOR  -> proof;
    XOR -> myAssume (); UnsafeXOR -> proof;
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s
          proof = wgSoundE' m ρ σ e1 σ1       -- σ1 ⊢ e1 (by IH)
                ? coherentEIncr m e1 σ1 σ2 π1 -- σ2 ⊢ e1 (since σ2 ≥ σ1)
                ? coherentEIncr m e1 σ2 σ' π2 -- σ' ⊢ e1 (since σ' ≥ σ2)

                ? wgSoundE' m ρ σ1 e2 σ2      -- σ2 ⊢ e2 (by IH)
                ? coherentEIncr m e2 σ2 σ' π2 -- σ' ⊢ e2 (since σ' ≥ σ2)

                ? π1 (outputWire e1) -- σ2[i1] == σ1[i1] (since σ2 ≥ σ1)

                ? liquidAssert (v1 == M.lookup' (outputWire e1) σ')
                ? liquidAssert (v2 == M.lookup' (outputWire e2) σ')
          v1 = M.lookup' (outputWire e1) σ1
          v2 = M.lookup' (outputWire e2) σ2

          {-@ π1 :: MapGE σ2 σ1 @-}
          π1 :: Int -> Proof
          π1 j = wgIncr m ρ σ1 e2 σ2 j

          {-@ π2 :: MapGE σ' σ2 @-}
          π2 :: Int -> Proof
          π2 j = trivial ? M.member j σ2 ? M.lookup' j σ'


  LEQLC e1 k w i -> if v1 == k
                    then proof
                       ? liquidAssert (vi == one)
                       ? liquidAssert (vw == zero)
                    else proof
                       ? liquidAssert (vi == zero)
                       ? liquidAssert (vw == 1/(v1-k))
                       ? liquidAssert (vw * (v1-k) == 1)   -- x/y * y /= x (in ℕ)

    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
          proof = wgSoundE' m ρ σ e1 σ1
                ? coherentEIncr m e1 σ1 σ' π
                ? π (outputWire e1) ? liquidAssert (v1 == M.lookup' (outputWire e1) σ')
                ? liquidAssert (v1 == M.lookup' (outputWire e1) σ')

          v1 = M.lookup' (outputWire e1) σ1
          vw = M.lookup' w σ'
          vi = M.lookup' i σ'

          {-@ π :: MapGE σ' σ1 @-}
          π :: Int -> Proof
          π j = (trivial ? M.member j σ1
                         ? M.lookup' j σ'
                         ? liquidAssert (j /= i && j /= w))
