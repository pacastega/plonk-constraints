{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module SetLemmas (ltLemma, disjLemma) where

import TypeAliases
import qualified Data.Set as S
import Utils
import Language.Haskell.Liquid.ProofCombinators

{-@ ltLemma :: a:Int -> b:Int -> s:S.Set (Btwn a b)
            -> y:{Int | y >= b} -> { not (S.member y s) } @-}
ltLemma :: Int -> Int -> S.Set Int -> Int -> Proof
ltLemma a b s x = ltAux a b (S.toList s) x

{-@ ltAux :: a:Int -> b:Int -> l:[Btwn a b]
          -> y:{Int | y >= b} -> { not (S.member y (S.listElts l)) } @-}
ltAux :: Int -> Int -> [Int] -> Int -> Proof
ltAux a b []     y = ()
ltAux a b (x:xs) y = ltAux a b xs y

{-@ disjLemma :: a:Int -> b:Int -> c:Int
              -> s1:S.Set (Btwn a b) -> s2:S.Set (Btwn b c)
              -> { disjoint s1 s2 } @-}
disjLemma :: Int -> Int -> Int -> S.Set Int -> S.Set Int -> Proof
disjLemma a b c s1 s2 = disjAux a b c (S.toList s1) (S.toList s2)

{-@ disjAux :: a:Int -> b:Int -> c:Int -> l1:[Btwn a b] -> l2:[Btwn b c]
            -> { disjoint (S.listElts l1) (S.listElts l2) } @-}
disjAux :: Int -> Int -> Int -> [Int] -> [Int] -> Proof
disjAux a b c xs []     = ()
disjAux a b c xs (y:ys) = ltAux a b xs y ? disjAux a b c xs ys
