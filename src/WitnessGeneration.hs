{-# OPTIONS -Wno-name-shadowing #-}
{-@ LIQUID "--reflection" @-}
module WitnessGeneration (extend, witnessGen, ValuationRefl) where
-- TODO: it shouldn't export ValuationRefl

import Utils (boolean)
import Vec
import DSL
import Semantics
import qualified Liquid.Data.Map as M


{-@ reflect updateWith @-}
updateWith :: Eq p => Maybe p -> Maybe p -> Maybe p
updateWith Nothing  _        = Nothing
updateWith (Just x) Nothing  = Just x
updateWith (Just x) (Just y) = if x == y then Just x else Nothing

extend :: ValuationRefl p -> (ValuationRefl p -> ValuationRefl p)
       -> ValuationRefl p
extend valuation hints = valuation ++ hints valuation

{-@ reflect foldl @-}

{-@ reflect witnessGen @-}
{-@ witnessGen :: m:Nat ->
                  [LDSL p (Btwn 0 m)] ->
                  ValuationRefl p ->
                  M.Map (Btwn 0 m) p @-}
witnessGen :: (Eq p, Fractional p) =>
              Int -> [LDSL p Int] -> ValuationRefl p -> M.Map Int p
witnessGen m programs strValuationRefl = valuation' where
    valuation' = foldl (\acc x -> update m strValuationRefl x acc)
                       M.empty programs

{-@ reflect update @-}
{-@ update :: m:Nat
           -> ValuationRefl p -> LDSL p (Btwn 0 m) -> M.Map (Btwn 0 m) p
           -> M.Map (Btwn 0 m) p @-}
update :: (Eq p, Fractional p) => Int
       -> ValuationRefl p -> LDSL p Int -> M.Map Int p -> M.Map Int p
update m _  (LWIRE _) valuation = valuation
update m sv (LVAR s τ i) valuation = M.alter (updateWith value) i valuation
  where value = case τ of -- value of ‘s’ in user-supplied valuation
          TF -> lookup s sv
          TBool -> lookup s sv >>= (\x -> if boolean x then Just x else Nothing)
update m _  (LCONST x i) valuation = M.alter (updateWith (Just x)) i valuation
update m sv (LADD p1 p2 i) valuation = M.alter (updateWith sum) i valuation'
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation'
  x2 = M.lookup (outputWire p2) valuation'
  sum = (+) <$> x1 <*> x2
update m sv (LSUB p1 p2 i) valuation = M.alter (updateWith sub) i valuation'
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation'
  x2 = M.lookup (outputWire p2) valuation'
  sub = (-) <$> x1 <*> x2
update m sv (LMUL p1 p2 i) valuation = M.alter (updateWith mult) i valuation'
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation'
  x2 = M.lookup (outputWire p2) valuation'
  mult = (*) <$> x1 <*> x2
update m sv (LDIV p1 p2 w i) valuation = valuation3
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation'
  x2 = M.lookup (outputWire p2) valuation' >>=
    (\x -> if x /= 0 then Just x else Nothing)
  div = (/) <$> x1 <*> x2
  wit = recip <$> x2
  valuation2 = M.alter (updateWith wit) w valuation'
  valuation3 = M.alter (updateWith div) i valuation2
update m sv (LADDC p1 k i) valuation = M.alter (updateWith sum) i valuation'
  where
  valuation' = update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation'
  sum = (+ k) <$> x1
update m sv (LMULC p1 k i) valuation = M.alter (updateWith mult) i valuation'
  where
  valuation' = update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation'
  mult = (* k) <$> x1
update m sv (LLINCOMB k1 p1 k2 p2 i) valuation = valuation''
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation'
  x2 = M.lookup (outputWire p2) valuation'
  val = (\x y -> k1*x + k2*y) <$> x1 <*> x2
  valuation'' = M.alter (updateWith val) i valuation'
update m sv (LNOT p1 i) valuation = M.alter (updateWith neg) i valuation'
  where
  valuation' = update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
  neg = (1 -) <$> x1
update m sv (LAND p1 p2 i) valuation = M.alter (updateWith and) i valuation'
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
  x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
  and = (*) <$> x1 <*> x2
update m sv (LOR  p1 p2 i) valuation = M.alter (updateWith or) i valuation'
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
  x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
  or = (\x y -> x + y - x*y) <$> x1 <*> x2
update m sv (LXOR p1 p2 i) valuation = M.alter (updateWith xor) i valuation'
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
  x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
  xor = (\x y -> x + y - 2*x*y) <$> x1 <*> x2
update m sv (LUnsafeNOT p1 i) valuation = M.alter (updateWith neg) i valuation'
  where
  valuation' = update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
  neg = (1 -) <$> x1
update m sv (LUnsafeAND p1 p2 i) valuation = M.alter (updateWith and) i valuation'
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
  x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
  and = (*) <$> x1 <*> x2
update m sv (LUnsafeOR  p1 p2 i) valuation = M.alter (updateWith or) i valuation'
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
  x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
  or = (\x y -> x + y - x*y) <$> x1 <*> x2
update m sv (LUnsafeXOR p1 p2 i) valuation = M.alter (updateWith xor) i valuation'
  where
  valuation' = update m sv p2 $ update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
  x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
  xor = (\x y -> x + y - 2*x*y) <$> x1 <*> x2

update m sv (LEQLC p1 k w i) valuation = valuation3
  where
  valuation1 = update m sv p1 valuation
  x1 = M.lookup (outputWire p1) valuation1
  witness  = (\x -> if x /= k then 1/(x-k) else 0) <$> x1
  result = (\x -> if x == k then 1 else 0) <$> x1
  valuation2 = M.alter (updateWith witness)  w valuation1
  valuation3 = M.alter (updateWith result)   i valuation2

update m sv (LNZERO p1 w) valuation = M.alter (updateWith witness) w valuation'
  where
  valuation' = update m sv p1 valuation
  witness = M.lookup (outputWire p1) valuation' >>=
    (\x -> if x /= 0 then Just (1/x) else Nothing)
update m sv (LBOOL p1) valuation = update m sv p1 valuation
update m sv (LEQA p1 p2) valuation = update m sv p2 $ update m sv p1 valuation


{-@ toVector :: m:Nat -> M.Map (Btwn 0 m) p -> VecN p m @-}
toVector :: Num p => Int -> M.Map Int p -> Vec p
toVector m valuation = aux m Nil where
  {-@ aux :: l:Nat -> acc:{Vec p | vvlen acc = m-l} -> VecN p m @-}
  aux 0 acc = acc
  aux l acc = aux (l-1) (Cons (M.findWithDefault 0 (l-1) valuation) acc)


-- -- TODO: ‘ensure (/= 0)’ should work for ‘x2’ in the case of ‘LDIV’ above
-- {-@ ensure :: p:(a -> Bool) -> x:a ->
--               {v:Maybe {w:a | p w} | v = (if (p x) then (Just x)
--                                                    else Nothing)} @-}
ensure :: (a -> Bool) -> a -> Maybe a
ensure p x = if p x then Just x else Nothing
