{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{- LIQUID "--ple" @-}
{-@ LIQUID "--no-positivity-check" @-}
{-@ LIQUID "--reflection" @-}
module Label where

import Constraints
import RefinementTypes()
import ArithmeticGates
import LogicGates
import Circuits

import Utils
import Vec
import DSL 
import qualified Data.Map as M



type Env p i = M.Map (DSL p) i

mmempty :: Env p i
-- mmempty = [] 
mmempty = M.empty 

malter :: (Eq p, Ord p) => (Maybe i -> Maybe i) -> DSL p -> Env p i -> Env p i 
-- malter f k env = env 
malter f k env = M.alter f k env

mlookup :: (Eq p, Ord p) => DSL p -> Env p i -> Maybe i 
mlookup k env = M.lookup k env



{-@ lazy label @-}
{-@ ignore label @-}
-- label each constructor with the index of the wire where its output will be
{-@ label :: DSL p ->
             (m:Nat, [LDSL p Int])<\m -> {l:[LDSL p (Btwn 0 m)] | true}> @-}
label :: Ord p => DSL p -> (Int, [LDSL p Int])
label program = (m, labeledPrograms) where
  (m, labeledPrograms, _) = label' program 0 mmempty

  -- combinator to label programs with 2 arguments that need recursive labelling
  {-@ label2 :: m0:Nat ->
                {arg1:DSL p | unpacked arg1} ->
                {arg2:DSL p | unpacked arg2} ->
                Env p (Btwn 0 m0) ->
                (m:{Int | m >= m0}, LDSL p Int, LDSL p Int, Env p Int)
                           <\m     -> {v:LDSL  p (Btwn 0 m)  | true},
                            \_ m   -> {v:LDSL  p (Btwn 0 m)  | true},
                            \_ _ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
  label2 :: Ord p => Int -> DSL p -> DSL p -> Env p Int ->
            (Int, LDSL p Int, LDSL p Int, Env p Int)
  label2 nextIndex arg1 arg2 env =
    let i = nextIndex
        (i1, [arg1'], env1) = label' arg1 i  env
        (i2, [arg2'], env2) = label' arg2 i1 env1
    in (i2, arg1', arg2', env2)

  add (k,v) = malter (\_ -> Just v) k

  {-@ label' :: program:(DSL p) ->
                m0:Nat -> Env p (Btwn 0 m0) ->
                (m:{Int | m >= m0}, [LDSL p Int], Env p Int)
             <\m   -> {l:[LDSL p (Btwn 0 m)] | unpacked program => len l = 1},
              \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
  label' :: Ord p => DSL p -> Int -> Env p Int
         -> (Int, [LDSL p Int], Env p Int)
  label' p nextIndex env = case mlookup p env of
    Just i  -> (nextIndex, [LWIRE i], env)
    Nothing -> let i = nextIndex in case p of

      VAR s -> (i+1, [LVAR s i], add (p,i) env)
      CONST x -> (i+1, [LCONST x i], add (p,i) env)

      ADD p1 p2 -> (i'+1, [LADD p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      SUB p1 p2 -> (i'+1, [LSUB p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      MUL p1 p2 -> (i'+1, [LMUL p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      DIV p1 p2 -> (i'+1, [LDIV p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env

      NOT p1    -> (i'+1, [LNOT p1' i'], add (p,i') env')
        where (i', [p1'], env') = label' p1 (i+1) env
      AND p1 p2 -> (i'+1, [LAND p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      OR  p1 p2 -> (i'+1, [LOR  p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      XOR p1 p2 -> (i'+1, [LXOR p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env

      UnsafeNOT p1    -> (i'+1, [LUnsafeNOT p1' i'], add (p,i') env')
        where (i', [p1'], env') = label' p1 (i+1) env
      UnsafeAND p1 p2 -> (i'+1, [LUnsafeAND p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      UnsafeOR  p1 p2 -> (i'+1, [LUnsafeOR  p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      UnsafeXOR p1 p2 -> (i'+1, [LUnsafeXOR p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env

      EQL p1 p2 -> label' (ISZERO (p1 `SUB` p2)) nextIndex env
      ISZERO p1 -> (w'+1, [LISZERO p1' w' i'], add (p,i') env')
        where (i', [p1'], env') = label' p1 i env; w' = i'+1
      EQLC p1 k -> (w'+1, [LEQLC p1' k w' i'], add (p,i') env')
        where (i', [p1'], env') = label' p1 i env; w' = i'+1

      NIL -> (i, [], env)
      CONS h ts -> (i'', h' ++ ts', env'')
        where (i',  h',  env')  = label' h  i  env
              (i'', ts', env'') = label' ts i' env'

