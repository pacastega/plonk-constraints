{-@ embed GHC.Num.Natural.Natural as int @-}
{-# LANGUAGE DataKinds #-}
module Main (main) where

import Interpolation (interpolateRoots)
import Data.FiniteField.PrimeField
import PrimitiveRoot
import qualified Data.Vector as V (fromList, zip, iterateN)
import Data.Poly

main :: IO ()
main = do

  let xs = V.iterateN 4 (* (primitiveRoot ^ (16 `div` 4))) 1
  let ys = V.fromList [7,-2,3,10]

  let q = interpolateRoots 17 4 ys :: VPoly (PrimeField 17)
  print q

  putStrLn "Actual - Desired"
  mapM_ (print . (\(x, y) -> (eval q x, y))) (V.zip xs ys)


  -- let x = recip 7 :: PrimeField 101
  -- print x
