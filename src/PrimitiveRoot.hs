{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
module PrimitiveRoot (PrimitiveRoot, primitiveRoot) where

import Data.FiniteField.PrimeField

class Num a => PrimitiveRoot a where
  primitiveRoot :: a

-- p = 5 = 2^2 + 1
instance PrimitiveRoot (PrimeField 5) where
  primitiveRoot = 2

-- p = 17 = 2^4 + 1
instance PrimitiveRoot (PrimeField 17) where
  primitiveRoot = 11

-- p = 257 = 2^8 + 1
instance PrimitiveRoot (PrimeField 257) where
  primitiveRoot = 75

-- p = 65537 = 2^16 + 1
instance PrimitiveRoot (PrimeField 65537) where
  primitiveRoot = 41790
