{-@ infix ! @-}
{-# OPTIONS -Wno-unused-matches -Wno-unused-imports
            -Wno-redundant-constraints #-}
{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module CompilerProof where

import Vec
import Constraints
import Circuits
import Utils

import GHC.TypeNats (KnownNat)
import PrimitiveRoot
import ArithmeticGates

import DSL

import Language.Haskell.Liquid.ProofCombinators

{-@ compileProof :: m:{v:Int | v >= 3} ->
                    program:LDSL p (Btwn Int 0 m) ->
                    input:VecN (F p) m ->
                    {semanticsAreCorrect m program input <=>
                     satisfies (nGates program) m input (compile m program)} @-}
compileProof :: (KnownNat p, PrimitiveRoot (F p)) =>
                Int -> LDSL p Int -> Vec (F p) -> Proof
compileProof m (LWIRE i) input
  =   semanticsAreCorrect m (LWIRE i) input
  === True
  === satisfies 0 m input (emptyCircuit m)
  *** QED
compileProof m (LCONST x i) input
  =   semanticsAreCorrect m (LCONST x i) input
  === input!i == x
  === satisfies 1 m input (constGate m x i)
  *** QED
compileProof m (LADD p1 p2 i) input =
  let i1 = outputWire p1; n1 = nGates p1
      correct1 = semanticsAreCorrect m p1 input

      i2 = outputWire p2; n2 = nGates p2
      correct2 = semanticsAreCorrect m p2 input

  in  semanticsAreCorrect m (LADD p1 p2 i) input
  === (correct1 && correct2 && input!i == input!i1 + input!i2)
      ? compileProof m p1 input ? compileProof m p2 input
  === (satisfies n1 m input (compile m p1) &&
       satisfies n2 m input (compile m p2) &&
       input!i == input!i1 + input!i2)
      ? satisfiesDistr n1 n2 m input (compile m p1) (compile m p2)
  === (satisfies (n1+n2) m input (append' (compile m p1) (compile m p2)) &&
       input!i == input!i1 + input!i2)
  === satisfies (1+n1+n2) m input (compile m (LADD p1 p2 i))
  *** QED
compileProof m (LMUL p1 p2 i) input =
  let i1 = outputWire p1; n1 = nGates p1
      correct1 = semanticsAreCorrect m p1 input

      i2 = outputWire p2; n2 = nGates p2
      correct2 = semanticsAreCorrect m p2 input

  in  semanticsAreCorrect m (LMUL p1 p2 i) input
  === (correct1 && correct2 && input!i == input!i1 * input!i2)
      ? compileProof m p1 input ? compileProof m p2 input
  === (satisfies n1 m input (compile m p1) &&
       satisfies n2 m input (compile m p2) &&
       input!i == input!i1 * input!i2)
      ? satisfiesDistr n1 n2 m input (compile m p1) (compile m p2)
  === (satisfies (n1+n2) m input (append' (compile m p1) (compile m p2)) &&
       input!i == input!i1 * input!i2)
  === satisfies (1+n1+n2) m input (compile m (LMUL p1 p2 i))
  *** QED


{-@ satisfiesDistr :: n1:Nat -> n2:Nat -> m:Nat ->
                      input:VecN (F p) m ->
                      c1:Circuit (F p) n1 m -> c2:Circuit (F p) n2 m ->
                      {satisfies (n1+n2) m input (append' c1 c2) <=>
                       satisfies n1 m input c1 && satisfies n2 m input c2} @-}
satisfiesDistr :: Int -> Int -> Int ->
                  Vec (F p) -> Circuit (F p) -> Circuit (F p) -> Proof
satisfiesDistr _  _  _ input []     c2 = trivial
satisfiesDistr n1 n2 m input (c:cs) c2 = satisfiesDistr (n1-1) n2 m input cs c2


-- {-@ satisfiesDistr :: n1:Nat -> n2:Nat -> n:{v:Nat | v == n1 + n2} -> m:Nat ->
--                       input:VecN (F p) m ->
--                       circ1:Circuit (F p) n1 m -> circ2:Circuit (F p) n2 m ->
--                 {satisfies n m input (join n1 n2 n m circ1 circ2) <=>
--                  satisfies n1 m input circ1 && satisfies n2 m input circ2} @-}
-- satisfiesDistr :: (KnownNat p) =>
--                   Int -> Int -> Int -> Int ->
--                   Vec (F p) ->
--                   Circuit (F p) -> Circuit (F p) ->
--                   Proof
-- satisfiesDistr 0 n2 n m input circ1 circ2
--   =   satisfies n2 m input (join 0 n2 n m circ1 circ2)
--       ? joinLeftId n2 n m circ1 circ2
--   === satisfies n2 m input circ2
--   === (satisfies 0 m input circ1 && satisfies n2 m input circ2)
--   *** QED
-- satisfiesDistr n1 n2 n m input circ1 circ2
--   -- satisfiesDistr (n1-1) n2 (n-1) m input circ1' circ2

--   =   satisfies n m input joined
--   === allRange 0 n p

--   === allRange 0 n p
--       ? allRangeAssoc 0 n n1 p
--   === (allRange 0 n1 (checkGate n  m input joined) &&
--        allRange n1 n (checkGate n  m input joined))
--   === (allRange 0 n1 (checkGate n1 m input circ1) &&
--        allRange n1 n (checkGate n2 m input circ2))

--   -- === (satisfies n1 m input circ1 && allRange n1 n p)
--   --     ? allRangeShifted n1 n n1 p
--   -- === (satisfies n1 m input circ1 && allRange 0 n2 p')
--   -- === (satisfies n1 m input circ1 && satisfies n2 m input circ2)
--   -- *** QED
--   where
--         joined = join n1 n2 n m circ1 circ2
--         p = checkGate n m input joined
--         -- p' = p . (+ n1)
--         ([Cons a1 as1, Cons b1 bs1, Cons c1 cs1],
--          [Cons qL1 qLs1, Cons qR1 qRs1, Cons qO1 qOs1,
--           Cons qM1 qMs1, Cons qC1 qCs1]) = circ1
--         -- ([a2,b2,c2], [qL2,qR2,qO2,qM2,qC2]) = circ2
--         circ1' = ([as1,bs1,cs1], [qLs1,qRs1,qOs1,qMs1,qCs1])


-- {-@ joinLeftId :: n2:Nat -> n:{v:Nat | v == n2} -> m:Nat ->
--                   c1:Circuit (F p) 0 m -> c2:Circuit (F p) n2 m ->
--                   {join 0 n2 n m c1 c2 = c2}@-}
-- joinLeftId :: Int -> Int -> Int ->
--               Circuit (F p) -> Circuit (F p) -> Proof
-- joinLeftId n2 n m c1@([Nil,Nil,Nil], [Nil,Nil,Nil,Nil,Nil])
--                   c2@([_,  _,  _],   [_,  _,  _,  _,  _])
--   = trivial


-- {-@ allRangeShifted :: a:Int -> b:{v:Int | a <= v} -> c:Int ->
--                        p:(Btwn Int a b -> Bool) ->
--                    {allRange a b p <=> allRange (a-c) (b-c) (p . (+ c))} @-}
-- allRangeShifted :: Int -> Int -> Int -> (Int -> Bool) -> Proof


{-@ indexShifted :: l1:Nat -> l2:Nat ->
                    v1:VecN a l1 -> v2:VecN a l2 -> i:Btwn Int 0 l2 ->
                    {(append v1 v2) ! (i+l1) = v2 ! i} @-}
indexShifted :: Int -> Int -> Vec a -> Vec a -> Int -> Proof
indexShifted 0 l2 Nil v2 i
  =   append Nil v2 ! (i+0)
  === v2 ! i
  *** QED
indexShifted l1 l2 (Cons v vs) v2 i
  =   append (Cons v vs) v2 ! (i+l1)
  === Cons v (append vs v2) ! (i+l1)
  === append vs v2 ! (i+l1-1)
      ? indexShifted (l1-1) l2 vs v2 i
  === v2 ! i
  *** QED


{-@ allRangeAssoc :: a:Int -> b:{v:Int | a <= v} ->
                     c:{v:Int | a <= v && v <= b} ->
                     p:(Btwn Int a b -> Bool) ->
               {allRange a b p <=> allRange a c p && allRange c b p}
               / [b-a] @-}
allRangeAssoc :: Int -> Int -> Int -> (Int -> Bool) -> Proof
allRangeAssoc a b c p
  | a == c    = trivial
  -- | otherwise = allRange a b p
  --           === (p a && allRange (a+1) b p) ? allRangeAssoc (a+1) b c p
  --           === (p a && allRange (a+1) c p && allRange c b p)
  --           === (allRange a c p && allRange c b p)
  --           *** QED
  | otherwise = allRangeAssoc (a+1) b c p
