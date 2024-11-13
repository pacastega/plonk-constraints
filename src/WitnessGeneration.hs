{-# OPTIONS -Wno-name-shadowing #-}
{-@ LIQUID "--reflection" @-}
module WitnessGeneration (witnessGen, Valuation) where

import Utils (boolean)
import Vec
import DSL
import qualified Data.Map as M


updateWith :: Eq p => Maybe p -> Maybe p -> Maybe p
updateWith Nothing  _        = Nothing
updateWith (Just x) Nothing  = Just x
updateWith (Just x) (Just y) = if x == y then Just x else Nothing

type Valuation p = M.Map String p

{-@ witnessGen :: m:Nat ->
                  [LDSL p (Btwn 0 m)] ->
                  Valuation p ->
                  VecN p m @-}
witnessGen :: (Eq p, Fractional p) =>
              Int -> [LDSL p Int] -> Valuation p -> Vec p
witnessGen m programs strValuation = toVector m valuation' where
    valuation' = foldl (flip $ update strValuation) M.empty programs

    {-@ update :: Valuation p -> LDSL p (Btwn 0 m) -> M.Map (Btwn 0 m) p
               -> M.Map (Btwn 0 m) p @-}
    update :: (Eq p, Fractional p) =>
              Valuation p -> LDSL p Int -> M.Map Int p -> M.Map Int p
    update _  (LWIRE _) valuation = valuation
    update sv (LVAR s i) valuation = M.alter (updateWith value) i valuation
      where value = M.lookup s sv -- value of ‘s’ in user-supplied valuation
    update _  (LCONST x i) valuation = M.alter (updateWith (Just x)) i valuation
    update sv (LADD p1 p2 i) valuation = M.alter (updateWith sum) i valuation'
      where
      valuation' = update sv p2 $ update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation'
      x2 = M.lookup (outputWire p2) valuation'
      sum = (+) <$> x1 <*> x2
    update sv (LSUB p1 p2 i) valuation = M.alter (updateWith sum) i valuation'
      where
      valuation' = update sv p2 $ update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation'
      x2 = M.lookup (outputWire p2) valuation'
      sum = (-) <$> x1 <*> x2
    update sv (LMUL p1 p2 i) valuation = M.alter (updateWith mult) i valuation'
      where
      valuation' = update sv p2 $ update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation'
      x2 = M.lookup (outputWire p2) valuation'
      mult = (*) <$> x1 <*> x2
    update sv (LDIV p1 p2 w i) valuation = valuation3
      where
      valuation' = update sv p2 $ update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation'
      x2 = M.lookup (outputWire p2) valuation' >>=
        (\x -> if x /= 0 then Just x else Nothing)
      div = (/) <$> x1 <*> x2
      wit = recip <$> x2
      valuation2 = M.alter (updateWith wit) w valuation'
      valuation3 = M.alter (updateWith div) i valuation2
    update sv (LNOT p1 i) valuation = M.alter (updateWith neg) i valuation'
      where
      valuation' = update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      neg = (1 -) <$> x1
    update sv (LAND p1 p2 i) valuation = M.alter (updateWith and) i valuation'
      where
      valuation' = update sv p2 $ update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
      and = (*) <$> x1 <*> x2
    update sv (LOR  p1 p2 i) valuation = M.alter (updateWith or) i valuation'
      where
      valuation' = update sv p2 $ update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
      or = (\x y -> x + y - x*y) <$> x1 <*> x2
    update sv (LXOR p1 p2 i) valuation = M.alter (updateWith xor) i valuation'
      where
      valuation' = update sv p2 $ update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
      xor = (\x y -> x + y - 2*x*y) <$> x1 <*> x2
    update sv (LUnsafeNOT p1 i) valuation = M.alter (updateWith neg) i valuation'
      where
      valuation' = update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      neg = (1 -) <$> x1
    update sv (LUnsafeAND p1 p2 i) valuation = M.alter (updateWith and) i valuation'
      where
      valuation' = update sv p2 $ update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
      and = (*) <$> x1 <*> x2
    update sv (LUnsafeOR  p1 p2 i) valuation = M.alter (updateWith or) i valuation'
      where
      valuation' = update sv p2 $ update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
      or = (\x y -> x + y - x*y) <$> x1 <*> x2
    update sv (LUnsafeXOR p1 p2 i) valuation = M.alter (updateWith xor) i valuation'
      where
      valuation' = update sv p2 $ update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
      xor = (\x y -> x + y - 2*x*y) <$> x1 <*> x2

    update sv (LNZERO p1 w) valuation = M.alter (updateWith witness) w valuation'
      where
      valuation' = update sv p1 valuation
      witness = M.lookup (outputWire p1) valuation' >>=
        (\x -> if x /= 0 then Just (1/x) else Nothing)

    update sv (LISZERO p1 w i) valuation = valuation3
      where
      valuation1 = update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation1
      witness  = (\x -> if x /= 0 then 1/x else 0) <$> x1
      result = (\x -> if x == 0 then 1 else 0) <$> x1
      valuation2 = M.alter (updateWith witness)  w valuation1
      valuation3 = M.alter (updateWith result)   i valuation2

    update sv (LEQLC p1 k w i) valuation = valuation3
      where
      valuation1 = update sv p1 valuation
      x1 = M.lookup (outputWire p1) valuation1
      witness  = (\x -> if x /= k then 1/(x-k) else 0) <$> x1
      result = (\x -> if x == k then 1 else 0) <$> x1
      valuation2 = M.alter (updateWith witness)  w valuation1
      valuation3 = M.alter (updateWith result)   i valuation2


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
