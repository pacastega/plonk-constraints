{-@ LIQUID "--reflection" @-}
module Liquid.Data.Map where

import Prelude hiding (lookup)

data Map k v = MTip | MBin k v (Map k v)

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
