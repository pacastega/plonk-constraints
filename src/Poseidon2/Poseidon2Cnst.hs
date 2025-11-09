{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Poseidon2.Poseidon2Cnst (Instance (..)) where

import Data.FiniteField.PrimeField
import GHC.Prim
import DSL

{-@ embed GHC.Prim.ByteArray# as int @-}

-- Some details of the implementation (e.g. the degree of the non-linear part of
-- the permutation) change depending on the size of the field.
-- For this reason, only some fields are sypported.

{-@ type ValidT = {t:Int | t = 2 || t = 3 || (t >= 4 && t <= 24 && t mod 4 = 0)} @-}
{-@ type ValidD = {d:Int | d = 3 || d = 5 || d = 7} @-}
{-@ type VecDSL' p N = {v:DSL p | typed v (TVec TF) && vlength v = N} @-}

{-@ data Instance fp = Ins { t :: ValidT
                           , d :: ValidD
                           , matInternalDiag :: VecDSL' fp t
                           , roundConstants_f1 :: [VecDSL'  fp t]
                           , roundConstants_p  :: [FieldDSL fp  ]
                           , roundConstants_f2 :: [VecDSL'  fp t]
                           }
@-}

data Instance fp = Ins { t :: Int
                       , d :: Int
                       , matInternalDiag :: DSL fp
                       , roundConstants_f1 :: [DSL fp]
                       , roundConstants_p  :: [DSL fp]
                       , roundConstants_f2 :: [DSL fp]
                       }
