{-@ LIQUID "--reflection" @-}
module Optimizations.RemoveConstants (removeConstants) where

import Optimizations.Base (Opt)
import DSL
import Utils (any')

{-@ removeConstants :: Opt p @-}
removeConstants :: (Fractional p, Eq p) => DSL p -> Maybe (DSL p)
removeConstants (ADD (MULC p1 k1) (MULC p2 k2))
  = Just $ LINCOMB k1 p1 k2 p2
removeConstants (ADD (MULC p1 k1) p2)
  = Just $ LINCOMB k1 p1 1 p2
removeConstants (ADD p1 (MULC p2 k2))
  = Just $ LINCOMB 1 p1 k2 p2
-- adding 0 is a no-op
removeConstants (ADD (CONST 0) p) = Just p
removeConstants (ADD p (CONST 0)) = Just p
removeConstants (ADD (BIT False) p) = Just p
removeConstants (ADD p (BIT False)) = Just p
-- subtracting 0 is a no-op
removeConstants (SUB p (CONST 0)) = Just p
-- adding a constant can be done more efficiently
removeConstants (ADD p (CONST k)) = Just (ADDC p k)
removeConstants (ADD (CONST k) p) = Just (ADDC p k)
removeConstants (ADD p (BIT True)) = Just (ADDC p 1)
removeConstants (ADD (BIT True) p) = Just (ADDC p 1)
removeConstants (SUB p (CONST k)) = Just (ADDC p (-k))
-- multiplying by 1 is a no-op
removeConstants (MUL (CONST 1) p) = Just p
removeConstants (MUL p (CONST 1)) = Just p
removeConstants (MUL (BIT True) p) = Just p
removeConstants (MUL p (BIT True)) = Just p
-- multiplying by 0 always returns 0
removeConstants (MUL (CONST 0) p) = Just (CONST 0)
removeConstants (MUL p (CONST 0)) = Just (CONST 0)
removeConstants (MUL (BIT False) p) = Just (CONST 0)
removeConstants (MUL p (BIT False)) = Just (CONST 0)
-- multiplying by a constant can be done more efficiently
removeConstants (MUL p (CONST k)) = Just (MULC p k)
removeConstants (MUL (CONST k) p) = Just (MULC p k)
-- dividing by 1 is a no-op
removeConstants (DIV p (CONST 1)) = Just p
removeConstants (DIV p (CONST k)) | k /= 0 = Just (MULC p (1/k))

-- checking equality against a constant can be done more efficiently
removeConstants (EQL p (CONST k)) = Just (EQLC p k)
removeConstants (EQL (CONST k) p) = Just (EQLC p k)

removeConstants _ = Nothing -- any other pattern is not a redex
