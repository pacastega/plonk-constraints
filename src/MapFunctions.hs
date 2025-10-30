module MapFunctions (lookup') where

import qualified Data.Map as M

{-@ ignore lookup' @-}
lookup' :: Ord k => k -> M.Map k a -> a
lookup' k m = case M.lookup k m of
  Just v  -> v
  Nothing -> error "key is not in the map"
