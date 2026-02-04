{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Liquid.Data.Map where

import Prelude hiding (lookup)
import Utils (elem')

import qualified Data.Set as S

data Map k v = MTip | MBin k v (Map k v)
  deriving (Show, Eq)

{-@ reflect empty @-}
empty :: Map k v
empty = MTip

{-@ reflect singleton @-}
singleton :: k -> v -> Map k v
singleton k v = MBin k v MTip

{-@ reflect lookup @-}
lookup :: Eq k => k -> Map k v -> Maybe v
lookup _ MTip = Nothing
lookup k (MBin k' v' m)
    | k == k'   = Just v'
    | otherwise = lookup k m

{-@ reflect alter @-}
alter :: Eq k => (Maybe v -> Maybe v) -> k -> Map k v -> Map k v
alter f k MTip = case f Nothing of
    Nothing -> MTip
    Just v  -> MBin k v MTip
alter f k (MBin k' v' m)
    | k == k' = case f (Just v') of
        Nothing  -> m
        Just v'' -> MBin k' v'' m
    | otherwise = MBin k' v' (alter f k m)

{-@ reflect insert @-}
{-@ insert :: key:k -> v -> m:Map k v
           -> {m':Map k v | keySet m' = S.union (keySet m) (S.singleton key)} @-}
insert :: k -> v -> Map k v -> Map k v
insert k v m = MBin k v m

{-@ reflect findWithDefault @-}
findWithDefault :: Eq k => v -> k -> Map k v -> v
findWithDefault def k m = case lookup k m of
    Just v  -> v
    Nothing -> def

{-@ reflect union @-}
union :: Map k v -> Map k v -> Map k v
union MTip          m = m
union (MBin k v m') m = MBin k v (union m' m)

{-@ reflect toList @-}
toList :: Map k v -> [(k,v)]
toList MTip         = []
toList (MBin k v m) = (k,v) : toList m

{-@ reflect fromList @-}
fromList :: [(k,v)] -> Map k v
fromList []        = MTip
fromList ((k,v):m) = MBin k v (fromList m)

{-@ reflect member @-}
member :: Ord k => k -> Map k v -> Bool
member k m = S.member k (keySet m)

{-@ reflect keys @-}
keys :: Map k v -> [k]
keys MTip         = []
keys (MBin k v m) = k : keys m

{-@ measure keySet @-}
keySet :: (Ord k) => Map k v -> S.Set k
keySet MTip = S.empty
keySet (MBin k v m) = S.singleton k `S.union` keySet m

{-@ reflect elems @-}
elems :: Map k v -> [v]
elems MTip         = []
elems (MBin k v m) = v : elems m

{-@ reflect lookup' @-}
{-@ lookup' :: key:k -> {m:Map k v | member key m} -> v @-}
lookup' :: Ord k => k -> Map k v -> v
lookup' k' (MBin k v m) = if k == k' then v else lookup' k' m
