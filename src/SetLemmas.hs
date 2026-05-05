{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module SetLemmas (ltLemma, disjLemma, subsetIncr) where

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

{-@ subsetIncr :: s1:S.Set Int -> s2:S.Set Int
               -> (x:{Int | S.member x s1} -> { S.member x s2 })
               -> { S.isSubsetOf s1 s2 } @-}
subsetIncr :: S.Set Int -> S.Set Int -> (Int -> Proof) -> Proof
subsetIncr s1 s2 = subsetIncr' (S.toList s1) (S.toList s2)

{-@ subsetIncr' :: xs:[Int] -> ys:[Int]
                -> (x:{Int | S.member x (S.fromList xs)} ->
                           { S.member x (S.fromList ys) })
                -> { S.isSubsetOf (S.fromList xs) (S.fromList ys) } @-}
subsetIncr' :: [Int] -> [Int] -> (Int -> Proof) -> Proof
subsetIncr' []     ys ge = ()
subsetIncr' (x:xs) ys ge = ge x ? subsetIncr' xs ys ge
