{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Optimizations.RemoveConstants (removeConstants) where

import Optimizations.Base (Opt)
import DSL
import Semantics
import Utils (any', liftA2', fmap')

import Data.Maybe (isJust)

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect removeConstants @-}
{-@ removeConstants :: Opt p @-}
removeConstants :: (Fractional p, Eq p) => DSL p -> Maybe (DSL p)
removeConstants e@(BIN op arg1 arg2) = case op of
  ADD -> case arg1 of
    -- linear combinations
    UN (MULC k1) p1 -> case arg2 of
      UN (MULC k2) p2 -> withProof (Just (BIN (LINCOMB k1 k2) p1 p2)) (wellTyped e)
      p2              -> withProof (Just (BIN (LINCOMB k1 1 ) p1 p2)) (wellTyped e)

    CONST 0 -> Just arg2
    CONST k -> Just (UN (ADDC k) arg2)

    p1 -> case arg2 of
      UN (MULC k2) p2 -> withProof (Just (BIN (LINCOMB 1 k2) p1 p2)) (wellTyped e)

      CONST 0 -> Just p1
      CONST k -> Just (UN (ADDC k) arg1)

      _ -> Nothing

  SUB -> case arg2 of
    -- subtracting 0 is a no-op
    CONST 0 -> Just arg1
    -- subtracting a constant can be done more efficiently
    CONST k -> Just (UN (ADDC (-k)) arg1)

    _ -> Nothing

  MUL -> case arg1 of
    CONST 1 -> Just arg2
    CONST 0 -> Just (CONST 0)
    CONST k -> Just (UN (MULC k) arg2)

    _ -> case arg2 of
      CONST 1 -> Just arg1
      CONST 0 -> Just (CONST 0)
      CONST k -> Just (UN (MULC k) arg1)

      _ -> Nothing

  DIV -> case arg2 of
    -- dividing by 1 is a no-op
    CONST 1 -> Just arg1

    _ -> Nothing

  EQL -> case arg1 of
    -- checking equality against a constant can be done more efficiently
    CONST k -> Just (UN (EQLC k) arg2)
    _ -> case arg2 of
      CONST k -> Just (UN (EQLC k) arg1)
      _       -> Nothing

  _ -> Nothing -- not a redex
removeConstants (UN op p1) = case op of
  (ADDC 0) -> Just p1
  (MULC 0) -> Just (CONST 0)
  (MULC 1) -> Just p1

  _ -> Nothing
removeConstants _ = Nothing -- any other pattern is not a redex

{-@ reflect isJust @-}

{-@ removeConstantsProof :: ρ:NameValuation p
         -> e1:{TypedDSL p | isJust (eval e1 ρ)}
         -> e2:{TypedDSL p | removeConstants e1 = Just e2}
         -> { eval e1 ρ = eval e2 ρ } @-}
removeConstantsProof :: (Fractional p, Eq p)
                     => NameValuation p -> DSL p -> DSL p -> Proof
removeConstantsProof ρ p@(BIN op arg1 arg2) p' = case op of
  ADD -> case arg1 of
    -- linear combinations
    UN (MULC k1) p1 -> case arg2 of
      UN (MULC k2) p2 -> case (eval p1 ρ, eval p2 ρ) of
        (Just (VF v1), Just (VF v2)) -> ()
      p2             -> case (eval p1 ρ, eval p2 ρ) of (Just _, Just _) -> (); _ -> ()

    CONST 0 -> case (eval arg2 ρ) of (Just _) -> (); _ -> ()
    CONST _ -> trivial

    p1 -> case arg2 of
      UN (MULC _) p2 -> case (eval p1 ρ, eval p2 ρ) of (Just _, Just _) -> (); _ -> ()

      CONST 0 -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
      CONST _ -> case (eval p1 ρ) of (Just _) -> (); _ -> ()

  SUB -> case (arg1,arg2) of
    -- subtracting 0 is a no-op
    (p1, CONST 0) -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
    -- subtracting a constant can be done more efficiently
    (p1, CONST _) -> case (eval p1 ρ) of (Just _) -> (); _ -> ()

  MUL -> case arg1 of
    CONST 1 -> case (eval arg2 ρ) of (Just _) -> (); _ -> ()
    CONST 0 -> case (eval arg2 ρ) of (Just _) -> (); _ -> ()
    CONST _ -> trivial

    p1 -> case arg2 of
      CONST 1 -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
      CONST 0 -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
      CONST _ -> case (eval p1 ρ) of (Just _) -> (); _ -> ()

  DIV -> case (arg1,arg2) of
    -- dividing by 1 is a no-op
    (p1, CONST 1) -> case (eval p1 ρ) of (Just _) -> (); _ -> ()

  EQL -> case (arg1,arg2) of
    -- checking equality against a constant can be done more efficiently
    (p1, CONST _) -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
    (CONST _, _) -> trivial


removeConstantsProof ρ (UN op p1) _ = case op of
  (ADDC _) -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
  (MULC _) -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
