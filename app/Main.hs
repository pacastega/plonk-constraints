{-@ embed GHC.Num.Natural.Natural as int @-}
-- {-@ embed Data.FiniteField.PrimeField * as FiniteField @-}
{-# LANGUAGE DataKinds #-}
module Main (main) where

import qualified Data.Vector as V (fromList, zip, iterateN)

import Interpolation (interpolateRoots)
import Data.FiniteField.PrimeField
import PrimitiveRoot
import Data.Poly

-- import ArithmeticGates
-- import Constraints

main :: IO ()
main = do

  let xs = V.iterateN 4 (* (primitiveRoot ^ (16 `div` 4))) 1
  let ys = V.fromList [7,-2,3,10]
  let q = interpolateRoots 17 4 ys :: VPoly (PrimeField 17)
  print q
  putStrLn "Actual - Desired"
  mapM_ (print . (\(x, y) -> (eval q x, y))) (V.zip xs ys)

  -- print $ satisfies 1 3 (V.fromList [2,3,5]) addGate -- True
  -- print $ satisfies 1 3 (V.fromList [2,3,6]) addGate -- False
  -- print $ satisfies 1 3 (V.fromList [5,3,10]) mulGate -- False
  -- print $ satisfies 1 3 (V.fromList [5,3,-2]) mulGate -- True
