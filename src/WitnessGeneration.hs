{-# OPTIONS -Wno-name-shadowing #-}
{-@ LIQUID "--reflection" @-}
module WitnessGeneration (witnessGen) where

import Utils (boolean)
import Vec
import DSL
import qualified Data.Map as M
import qualified Data.Set as S


updateWith :: Eq p => Maybe p -> Maybe p -> Maybe p
updateWith Nothing  _        = Nothing
updateWith (Just x) Nothing  = Just x
updateWith (Just x) (Just y) = if x == y then Just x else Nothing


{-@ witnessGen :: m:Nat ->
                  program:LDSL p (Btwn 0 m) ->
                  ({v : Btwn 0 m | S.member v (lwires program)} -> p) ->
                  VecN p m @-}
witnessGen :: (Eq p, Fractional p) => Int -> LDSL p Int -> (Int -> p) -> Vec p
witnessGen m program valuation = toVector m $ update program valuation' where
    valuation' = toMap (lwires program) valuation

    update (LWIRE _) valuation = valuation
    update (LCONST x i) valuation = M.alter (updateWith (Just x)) i valuation
    update (LADD p1 p2 i) valuation = M.alter (updateWith sum) i valuation'
      where
      valuation' = update p2 $ update p1 valuation
      x1 = M.lookup (outputWire p1) valuation'
      x2 = M.lookup (outputWire p2) valuation'
      sum = (+) <$> x1 <*> x2
    update (LSUB p1 p2 i) valuation = M.alter (updateWith sum) i valuation'
      where
      valuation' = update p2 $ update p1 valuation
      x1 = M.lookup (outputWire p1) valuation'
      x2 = M.lookup (outputWire p2) valuation'
      sum = (-) <$> x1 <*> x2
    update (LMUL p1 p2 i) valuation = M.alter (updateWith mult) i valuation'
      where
      valuation' = update p2 $ update p1 valuation
      x1 = M.lookup (outputWire p1) valuation'
      x2 = M.lookup (outputWire p2) valuation'
      mult = (*) <$> x1 <*> x2
    update (LDIV p1 p2 i) valuation = M.alter (updateWith div) i valuation'
      where
      valuation' = update p2 $ update p1 valuation
      x1 = M.lookup (outputWire p1) valuation'
      x2 = M.lookup (outputWire p2) valuation' >>=
        (\x -> if x /= 0 then Just x else Nothing)
      div = (/) <$> x1 <*> x2
    update (LNOT p1 i) valuation = M.alter (updateWith neg) i valuation'
      where
      valuation' = update p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      neg = (1 -) <$> x1
    update (LAND p1 p2 i) valuation = M.alter (updateWith and) i valuation'
      where
      valuation' = update p2 $ update p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
      and = (*) <$> x1 <*> x2
    update (LOR  p1 p2 i) valuation = M.alter (updateWith or) i valuation'
      where
      valuation' = update p2 $ update p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
      or = (\x y -> x + y - x*y) <$> x1 <*> x2
    update (LXOR p1 p2 i) valuation = M.alter (updateWith xor) i valuation'
      where
      valuation' = update p2 $ update p1 valuation
      x1 = M.lookup (outputWire p1) valuation' >>= ensure boolean
      x2 = M.lookup (outputWire p2) valuation' >>= ensure boolean
      xor = (\x y -> x + y - 2*x*y) <$> x1 <*> x2

    update (LISZERO p1 w i) valuation = valuation3
      where
      valuation1 = update p1 valuation
      x1 = M.lookup (outputWire p1) valuation1
      witness  = (\x -> if x /= 0 then 1/x else 0) <$> x1
      result = (\x -> if x == 0 then 1 else 0) <$> x1
      valuation2 = M.alter (updateWith witness)  w valuation1
      valuation3 = M.alter (updateWith result)   i valuation2


{-@ toVector :: m:Nat -> M.Map (Btwn 0 m) p -> VecN p m @-}
toVector :: Num p => Int -> M.Map Int p -> Vec p
toVector m valuation = aux m Nil where
  {-@ aux :: l:Nat -> acc:{Vec p | vvlen acc = m-l} -> VecN p m @-}
  aux 0 acc = acc
  aux l acc = aux (l-1) (Cons (M.findWithDefault 0 (l-1) valuation) acc)


{-@ toMap :: xs:S.Set a -> ({v:a | S.member v xs} -> b) ->
             M.Map {v:a | S.member v xs} b @-}
toMap :: Ord a => S.Set a -> (a -> b) -> M.Map a b
toMap xs f = M.fromList $ map (\x -> (x, f x)) $ S.toList xs

{-@ assume S.toList :: xs:S.Set a -> [{v:a | S.member v xs}] @-}


-- -- TODO: ‘ensure (/= 0)’ should work for ‘x2’ in the case of ‘LDIV’ above
-- {-@ ensure :: p:(a -> Bool) -> x:a ->
--               {v:Maybe {w:a | p w} | v = (if (p x) then (Just x)
--                                                    else Nothing)} @-}
ensure :: (a -> Bool) -> a -> Maybe a
ensure p x = if p x then Just x else Nothing
