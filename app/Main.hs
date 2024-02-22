{-@ embed GHC.Num.Natural.Natural as int @-}
{-# LANGUAGE DataKinds #-}
module Main (main) where

import Interpolation (interpolate)
import Data.FiniteField.PrimeField
import qualified Data.Vector as V (fromList, zip)
import Data.Poly

main :: IO ()
main = do

  let xs = V.fromList [1,2,3]
  let ys = V.fromList [7,-2,3]

  let q = interpolate 3 xs ys :: VPoly (PrimeField 101)
  print q

  putStrLn "Actual - Desired"
  mapM_ (print . (\(x, y) -> (eval q x, y))) (V.zip xs ys)


  -- let x = recip 7 :: PrimeField 101
  -- print x
