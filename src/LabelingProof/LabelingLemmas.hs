{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module LabelingProof.LabelingLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

import Utils
import TypeAliases

import Constraints
import DSL
import Label
import WitnessGeneration
import Semantics

import MapLemmas
import SetLemmas
import Language.Haskell.Liquid.ProofCombinators

-- labeling produces well-formed expressions -----------------------------------

{-@ labelWF :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
            -> m:{Int | m >= m0} -> e':LDSL p Int
            -> λ':{LabelEnv p Int | label' e m0 λ = (m, e', λ')}
            -> { wfE e' }
             / [size e] @-}
labelWF :: (Num p, Ord p) => DSL p -> Int -> LabelEnv p Int
        -> Int -> LDSL p Int -> LabelEnv p Int
        -> Proof
labelWF e m0 λ m e' λ' = case e of
  VAR s _ -> case M.lookup s λ of
    Nothing -> trivial
    Just _  -> trivial
  CONST _ -> trivial
  BOOL True  -> trivial
  BOOL False -> trivial

  UN op e1 -> case op of
    BoolToF -> labelWF e1                  m0 λ m  e1' λ1
      where (_, e1', λ1) = label' e1 m0 λ
    ISZERO  -> labelWF (UN (EQLC zero) e1) m0 λ m  e'  λ'
    EQLC k  -> labelWF e1                  m0 λ i' e1' λ1
             ? ltLemma 0 i' used w' ? ltLemma 0 i' used i'
      where (i', e1', λ1) = label' e1 m0 λ
            w' = i'+1

            {-@ used :: S.Set (Btwn 0 i') @-}
            used :: S.Set Int
            used = wiresE e1'

    _ -> labelWF e1 m0 λ i' e1' λ1 ? ltLemma 0 i' used i'
      where (i', e1', λ1) = label' e1 m0 λ

            {-@ used :: S.Set (Btwn 0 i') @-}
            used :: S.Set Int
            used = wiresE e1'

  BIN op e1 e2 -> case op of
    DIV -> labelWF e1 m0 λ  i1 e1' λ1
         ? labelWF e2 i1 λ1 i2 e2' λ2
         ? ltLemma 0 i1 used1 i2 ? ltLemma i1 i2 used2 i2
         ? disjLemma 0 i1 i2 used1 used2
         ? ltLemma 0 i2 (used1 `S.union` used2) i
         ? ltLemma 0 i2 (used1 `S.union` used2) w
      where (i1, e1', λ1) = label' e1 m0 λ
            (i2, e2', λ2) = label' e2 i1 λ1

            (LDIV _ _ w i) = e'

            {-@ used1 :: S.Set (Btwn 0 i1) @-}
            used1 :: S.Set Int
            used1 = wiresE e1'

            {-@ used2 :: S.Set (Btwn i1 i2) @-}
            used2 :: S.Set Int
            used2 = wiresE e2'

    EQL -> labelWF e1 m0 λ  i1 e1' λ1
         ? labelWF e2 i1 λ1 i2 e2' λ2
         ? ltLemma 0 i1 used1 i2 ? ltLemma i1 i2 used2 i2
         ? disjLemma 0 i1 i2 used1 used2
         ? ltLemma 0 i2 (used1 `S.union` used2) i
         ? ltLemma 0 i2 (used1 `S.union` used2) w
      where (i1, e1', λ1) = label' e1 m0 λ
            (i2, e2', λ2) = label' e2 i1 λ1

            (LEQLC _ _ w i) = e'

            {-@ used1 :: S.Set (Btwn 0 i1) @-}
            used1 :: S.Set Int
            used1 = wiresE e1'

            {-@ used2 :: S.Set (Btwn i1 i2) @-}
            used2 :: S.Set Int
            used2 = wiresE e2'

    _ -> labelWF e1 m0 λ  i1 e1' λ1
       ? labelWF e2 i1 λ1 i2 e2' λ2
       ? ltLemma 0 i1 used1 i2 ? ltLemma i1 i2 used2 i2
       ? disjLemma 0 i1 i2 used1 used2
      where (i1, e1', λ1) = label' e1 m0 λ
            (i2, e2', λ2) = label' e2 i1 λ1

            {-@ used1 :: S.Set (Btwn 0 i1) @-}
            used1 :: S.Set Int
            used1 = wiresE e1'

            {-@ used2 :: S.Set (Btwn i1 i2) @-}
            used2 :: S.Set Int
            used2 = wiresE e2'

  NIL _ -> trivial
  CONS e es -> labelWF e  m0 λ  i1 e'  λ1
             ? labelWF es i1 λ1 i2 es' λ2
             ? disjLemma 0 i1 i2 usedH usedTs
    where (i1, e',  λ1) = label' e  m0 λ
          (i2, es', λ2) = label' es i1 λ1

          {-@ usedH :: S.Set (Btwn 0 i1) @-}
          usedH :: S.Set Int
          usedH = wiresE e'

          {-@ usedTs :: S.Set (Btwn i1 i2) @-}
          usedTs :: S.Set Int
          usedTs = wiresE es'


-- labeling produces well-typed expressions (of the same type) -----------------

{-@ labelType :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
              -> m:Int -> e':LDSL p Int
              -> λ':{LabelEnv p Int | label' e m0 λ = (m, e', λ')}
              -> { inferType' e' = inferType e } @-}
labelType :: (Num p, Ord p) => DSL p -> Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
labelType e m0 λ _ _ _ = case label' e m0 λ of (_, e', _) -> trivial


{-@ labelTyped :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
               -> m:Int -> e':LDSL p Int
               -> λ':{LabelEnv p Int | label' e m0 λ = (m, e', λ')}
               -> { wellTyped' e' } @-}
labelTyped :: (Num p, Ord p) => DSL p -> Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Proof
labelTyped e m0 λ m e' λ' = case inferType e of
  Just _ -> labelType e m0 λ m e' λ'


-- expressions are labeled inductively by their subexpressions -----------------

-- if e1↝e1' and ↑e1↝e' then e' = LBoolToF e1'
{-@ labelCast :: m0:Nat -> e1:DSL p -> λ:LabelEnv p (Btwn 0 m0)

              -> m1:{Int | m1 >= m0}
              -> e1':LDSL p (Btwn 0 m1)
              -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

              -> m:{Int | m >= m1}
              -> e':LDSL p (Btwn 0 m)
              -> λ':{LabelEnv p (Btwn 0 m) |
                              label' (UN BoolToF e1) m0 λ = (m, e', λ')}
              -> { e' = LBoolToF e1' } @-}
labelCast :: (Num p, Ord p) => Int -> DSL p -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
labelCast m0 e1 λ m1 e1' λ1 _m e' _λ' = case e' of
  LBoolToF _ -> trivial


-- if e1↝e1', e2↝e2' and e1/e2↝e' then ∃w,i . e' = LDIV e1' e2' w i
{-@ labelDiv :: m0:Nat -> e1:DSL p -> e2:DSL p -> λ:LabelEnv p (Btwn 0 m0)

             -> m1:{Int | m1 >= m0}
             -> e1':LDSL p (Btwn 0 m1)
             -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

             -> m2:{Int | m2 >= m1}
             -> e2':LDSL p (Btwn 0 m2)
             -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

             -> m:{Int | m >= m2}
             -> e':LDSL p (Btwn 0 m)
             -> λ':{LabelEnv p (Btwn 0 m) |
                             label' (BIN DIV e1 e2) m0 λ = (m, e', λ')}
             -> (w::Btwn 0 m, i:{Btwn 0 m | e' = LDIV e1' e2' w i}) @-}
labelDiv :: (Num p, Ord p) => Int -> DSL p -> DSL p -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> (Int, Int)
labelDiv m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 _m e' _λ' = case e' of
  LDIV _ _ w i -> (w, i)


-- if e1↝e1' and □e1↝e' then ∃w,i . e' = LUN □ e1' i
{-@ labelUn :: m0:Nat -> e1:DSL p -> λ:LabelEnv p (Btwn 0 m0) -> op:UnOp' p

            -> m1:{Int | m1 >= m0}
            -> e1':LDSL p (Btwn 0 m1)
            -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

            -> m:{Int | m >= m1}
            -> e':LDSL p (Btwn 0 m)
            -> λ':{LabelEnv p (Btwn 0 m) |
                            label' (UN op e1) m0 λ = (m, e', λ')}
            -> i:{Btwn 0 m | e' = LUN op e1' i} @-}
labelUn :: (Num p, Ord p) => Int -> DSL p -> LabelEnv p Int -> UnOp p
        -> Int -> LDSL p Int -> LabelEnv p Int
        -> Int -> LDSL p Int -> LabelEnv p Int
        -> Int
labelUn m0 e1 λ op m1 e1' λ1 _m e' _λ' = case op of
  EQLC _  -> error "impossible"
  ISZERO  -> error "impossible"
  BoolToF -> error "impossible"
  _ -> case e' of LUN _ _ i -> i


-- if e1↝e1', e2↝e2' and e1⮾e2↝e' then ∃i . e' = LBIN ⮾ e1' e2' i
{-@ labelBin :: m0:Nat -> e1:DSL p -> e2:DSL p -> λ:LabelEnv p (Btwn 0 m0)
             -> op:BinOp' p

             -> m1:{Int | m1 >= m0}
             -> e1':LDSL p (Btwn 0 m1)
             -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

             -> m2:{Int | m2 >= m1}
             -> e2':LDSL p (Btwn 0 m2)
             -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

             -> m:{Int | m >= m2}
             -> e':LDSL p (Btwn 0 m)
             -> λ':{LabelEnv p (Btwn 0 m) |
                             label' (BIN op e1 e2) m0 λ = (m, e', λ')}
             -> i:{Btwn 0 m | e' = LBIN op e1' e2' i} @-}
labelBin :: (Num p, Ord p) => Int -> DSL p -> DSL p -> LabelEnv p Int -> BinOp p
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int
labelBin m0 e1 e2 λ op m1 e1' λ1 m2 e2' λ2 _m e' _λ' = case op of
  EQL -> error "impossible"
  DIV -> error "impossible"
  _ -> case e' of LBIN _ _ _ i -> i


-- if e1↝e1', e2↝e2' and e1==e2↝e' then ∃d,w,i . e' = LEQLC (LBIN SUB e1' e2' d) 0 w i
{-@ labelEql :: m0:Nat -> e1:DSL p -> e2:DSL p -> λ:LabelEnv p (Btwn 0 m0)

             -> m1:{Int | m1 >= m0}
             -> e1':LDSL p (Btwn 0 m1)
             -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

             -> m2:{Int | m2 >= m1}
             -> e2':LDSL p (Btwn 0 m2)
             -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

             -> m:{Int | m >= m2}
             -> e':LDSL p (Btwn 0 m)
             -> λ':{LabelEnv p (Btwn 0 m) |
                             label' (BIN EQL e1 e2) m0 λ = (m, e', λ')}
             -> (d::Btwn 0 m, w::Btwn 0 m, i:{Btwn 0 m | e' = LEQLC (LBIN SUB e1' e2' d) 0 w i}) @-}
labelEql :: (Num p, Ord p) => Int -> DSL p -> DSL p -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> (Int, Int, Int)
labelEql m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 _m e' _λ' = case e' of
  LEQLC (LBIN SUB _ _ d) _ w i -> (d, w, i)


-- if e1↝e1' and e1==k↝e' then ∃w,i . e' = LEQLC e1' k w i
{-@ labelIsk :: m0:Nat -> e1:DSL p -> λ:LabelEnv p (Btwn 0 m0) -> k:p

             -> m1:{Int | m1 >= m0}
             -> e1':LDSL p (Btwn 0 m1)
             -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

             -> m:{Int | m >= m1}
             -> e':LDSL p (Btwn 0 m)
             -> λ':{LabelEnv p (Btwn 0 m) |
                             label' (UN (EQLC k) e1) m0 λ = (m, e', λ')}
             -> (w::Btwn 0 m, i:{Btwn 0 m | e' = LEQLC e1' k w i}) @-}
labelIsk :: (Num p, Ord p) => Int -> DSL p -> LabelEnv p Int -> p
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> (Int, Int)
labelIsk m0 e1 λ k m1 e1' λ1 _m e' _λ' = case e' of
  LEQLC _ _ w i -> (w, i)


-- if e1↝e1' and e1==0↝e' then ∃w,i . e' = LEQLC e1' 0 w i
{-@ labelIs0 :: m0:Nat -> e1:DSL p -> λ:LabelEnv p (Btwn 0 m0)

             -> m1:{Int | m1 >= m0}
             -> e1':LDSL p (Btwn 0 m1)
             -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

             -> m:{Int | m >= m1}
             -> e':LDSL p (Btwn 0 m)
             -> λ':{LabelEnv p (Btwn 0 m) |
                             label' (UN ISZERO e1) m0 λ = (m, e', λ')}
             -> (w::Btwn 0 m, i:{Btwn 0 m | e' = LEQLC e1' 0 w i}) @-}
labelIs0 :: (Num p, Ord p) => Int -> DSL p -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> (Int, Int)
labelIs0 m0 e1 λ m1 e1' λ1 _m e' _λ' = case e' of
  LEQLC _ _ w i -> (w, i)


-- if e1↝e1', e2↝e2' and e1::e2↝e' then e' = LCONS e1' e2'
{-@ labelCons :: m0:Nat -> e1:DSL p -> e2:DSL p -> λ:LabelEnv p (Btwn 0 m0)

              -> m1:{Int | m1 >= m0}
              -> e1':LDSL p (Btwn 0 m1)
              -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

              -> m2:{Int | m2 >= m1}
              -> e2':LDSL p (Btwn 0 m2)
              -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

              -> m:{Int | m >= m2}
              -> e':LDSL p (Btwn 0 m)
              -> λ':{LabelEnv p (Btwn 0 m) |
                              label' (CONS e1 e2) m0 λ = (m, e', λ')}
              -> { e' = LCONS e1' e2' } @-}
labelCons :: (Num p, Ord p) => Int -> DSL p -> DSL p -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
labelCons m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 _m e' _λ' = case e' of
   LCONS _ _ -> trivial


-- labeling never decreases the bound on used wires ----------------------------

{-@ labelIncUn :: op:UnOp p -> e1:{DSL p | wellTyped (UN op e1)} -> m0:Nat -> λ:LabelEnv p Int
               -> m1:Int -> e1':LDSL p Int -> λ1:{LabelEnv p Int | label' e1 m0 λ = (m1, e1', λ1)}
               ->  m:Int ->  e':LDSL p Int -> λ':{LabelEnv p Int | label' (UN op e1) m0 λ = (m, e', λ')}
               -> { m >= m1 } @-}
labelIncUn :: Num p => UnOp p -> DSL p -> Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Proof
labelIncUn op _ _ _ _ _ _ _ _ _ = case op of
  BoolToF -> ()
  ISZERO  -> ()
  EQLC _  -> ()
  _       -> ()


{-@ labelIncBin :: op:BinOp p
                -> e1:DSL p -> e2:{DSL p | wellTyped (BIN op e1 e2)}
                -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

                -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
                -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

                -> m2:Nat -> e2':LDSL p (Btwn 0 m2)
                -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                ->  m:Nat ->  e':LDSL p (Btwn 0 m)
                -> λ':{LabelEnv p (Btwn 0 m) | label' (BIN op e1 e2) m0 λ = (m, e', λ')}
                -> { m >= m2 && m2 >= m1 } @-}
labelIncBin :: (Num p, Ord p) => BinOp p -> DSL p -> DSL p -> Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Proof
labelIncBin op e1 e2 m0 λ m1 _e1' λ1 m2 _e2' _λ2 m _e' _λ'
  = trivial ? case label' e1 m0 λ  of (m1,_,_) -> m1
            ? case label' e2 m1 λ1 of (m2,_,_) -> m2
            ? case op of
                DIV -> liquidAssert (m > m2)
                EQL -> liquidAssert (m > m2)
                _   -> liquidAssert (m > m2)


{-@ labelIncCons :: e1:DSL p -> e2:{DSL p | wellTyped (CONS e1 e2)}
                 -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

                 -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
                 -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

                 -> m2:Nat -> e2':LDSL p (Btwn 0 m2)
                 -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                 -> m:Nat -> e':LDSL p (Btwn 0 m)
                 -> λ':{LabelEnv p (Btwn 0 m) | label' (CONS e1 e2) m0 λ = (m, e', λ')}
                 -> { m >= m2 && m2 >= m1 } @-}
labelIncCons :: (Num p, Ord p) => DSL p -> DSL p -> Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Proof
labelIncCons e1 e2 m0 λ m1 _e1' λ1 m2 _e2' _λ2 m _e' _λ'
  = trivial ? case label' e1 m0 λ  of (m1,_,_) -> m1
            ? case label' e2 m1 λ1 of (m2,_,_) -> m2
