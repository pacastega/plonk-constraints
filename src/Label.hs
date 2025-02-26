{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Label (label) where

import TypeAliases
import DSL
import Utils

import qualified Data.Map as M

type Env p i = M.Map (DSL p) i

{-@ label :: TypedDSL p
          -> Store p
          -> (m:Nat, [LDSL p Int], [LDSL p Int])
                  <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
                   \_ m -> {l:[LDSL p (Btwn 0 m)] | true}> @-}
label :: (Num p, Ord p) => DSL p -> Store p -> (Int, [LDSL p Int], [LDSL p Int])
label program store = (m, labeledPrograms, labeledStore) where
  (m', labeledStore, env') = labelStore store 0 M.empty
  (m, labeledPrograms, _) = label' program m' env' Nothing

{-@ labelStore :: Store p -> m0:Nat -> Env p (Btwn 0 m0)
               -> (m:{Int | m >= m0}, [LDSL p Int], Env p Int)
                      <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
                       \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
labelStore :: (Num p, Ord p) =>
              Store p -> Int -> Env p Int -> (Int, [LDSL p Int], Env p Int)
labelStore [] nextIndex env = (nextIndex, [], env)
labelStore (def:ss) nextIndex env =
  let i = nextIndex
      (i', def', env') = labelStore' def i env
      (i'', ss', env'') = labelStore ss i' env'
  in (i'', def' ++ ss', env'')

-- combinator to label programs with 2 arguments that need recursive labelling
{-@ lazy label2 @-}
{-@ label2 :: m0:Nat -> ScalarDSL p -> ScalarDSL p -> Env p (Btwn 0 m0) ->
              (m:{Int | m >= m0}, LDSL p Int, LDSL p Int, Env p Int)
                         <\m     -> {v:LDSL  p (Btwn 0 m)  | true},
                          \_ m   -> {v:LDSL  p (Btwn 0 m)  | true},
                          \_ _ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
label2 :: (Num p, Ord p) => Int -> DSL p -> DSL p -> Env p Int ->
          (Int, LDSL p Int, LDSL p Int, Env p Int)
label2 nextIndex arg1 arg2 env =
  let i = nextIndex
      (i1, [arg1'], env1) = label' arg1 i  env  Nothing
      (i2, [arg2'], env2) = label' arg2 i1 env1 Nothing
  in (i2, arg1', arg2', env2)


add :: Ord k => (k, v) -> M.Map k v -> M.Map k v
add (k,v) = M.alter (\_ -> Just v) k


{-@ lazy label' @-}
{-@ label' :: program:TypedDSL p ->
              m0:Nat -> Env p (Btwn 0 m0) ->
              Maybe (Btwn 0 m0) ->
              (m:{Int | m >= m0}, [LDSL p Int], Env p Int)
           <\m   -> {l:[LDSL p (Btwn 0 m)] | scalar program => len l = 1},
            \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
label' :: (Num p, Ord p) => DSL p -> Int -> Env p Int -> Maybe Int
       -> (Int, [LDSL p Int], Env p Int)
label' p nextIndex env requested = case M.lookup p env of
  Just i  -> (nextIndex, [LWIRE i], env)
  Nothing -> let i = nextIndex in case p of

    VAR s _ -> withOutputWire i requested p (LVAR s) env
    CONST x -> withOutputWire i requested p (LCONST x) env
    BOOLEAN b  -> label' (CONST $ fromIntegral $ fromEnum b) nextIndex env requested

    ADD p1 p2 -> withOutputWire i' requested p (LADD p1' p2') env
      where (i', p1', p2', env') = label2 i p1 p2 env
    SUB p1 p2 -> withOutputWire i' requested p (LSUB p1' p2') env
      where (i', p1', p2', env') = label2 i p1 p2 env
    MUL p1 p2 -> withOutputWire i' requested p (LMUL p1' p2') env
      where (i', p1', p2', env') = label2 i p1 p2 env
    DIV p1 p2 -> withOutputWire i' requested p (LDIV p1' p2' w') env
      where (w', p1', p2', env') = label2 i p1 p2 env; i' = w'+1
    ADDC p1 k -> withOutputWire i' requested p (LADDC p1' k) env
      where (i', [p1'], env') = label' p1 i env Nothing
    MULC p1 k -> withOutputWire i' requested p (LMULC p1' k) env
      where (i', [p1'], env') = label' p1 i env Nothing
    LINCOMB k1 p1 k2 p2 -> withOutputWire i' requested p (LLINCOMB k1 p1' k2 p2') env
      where (i', p1', p2', env') = label2 i p1 p2 env

    NOT p1    -> withOutputWire i' requested p (LNOT p1') env
      where (i', [p1'], env') = label' p1 i env Nothing
    AND p1 p2 -> withOutputWire i' requested p (LAND p1' p2') env
      where (i', p1', p2', env') = label2 i p1 p2 env
    OR  p1 p2 -> withOutputWire i' requested p (LOR p1' p2') env
      where (i', p1', p2', env') = label2 i p1 p2 env
    XOR p1 p2 -> withOutputWire i' requested p (LXOR p1' p2') env
      where (i', p1', p2', env') = label2 i p1 p2 env

    UnsafeNOT p1    -> withOutputWire i' requested p (LUnsafeNOT p1') env
      where (i', [p1'], env') = label' p1 i env Nothing
    UnsafeAND p1 p2 -> withOutputWire i' requested p (LUnsafeAND p1' p2') env
      where (i', p1', p2', env') = label2 i p1 p2 env
    UnsafeOR  p1 p2 -> withOutputWire i' requested p (LUnsafeOR  p1' p2') env
      where (i', p1', p2', env') = label2 i p1 p2 env
    UnsafeXOR p1 p2 -> withOutputWire i' requested p (LUnsafeXOR p1' p2') env
      where (i', p1', p2', env') = label2 i p1 p2 env

    ISZERO p1 -> label' (EQLC p1 0) nextIndex env Nothing
    EQL p1 p2 -> label' (ISZERO (p1 `SUB` p2)) nextIndex env Nothing
    EQLC p1 k -> withOutputWire i' requested p (LEQLC p1' k w') env
      where (w', [p1'], env') = label' p1 i env Nothing; i' = w'+1

    NIL _ -> (i, [], env)
    CONS h ts -> (i'', h' ++ ts', env'')
      where (i',  h',  env')  = label' h  i  env Nothing
            (i'', ts', env'') = label' ts i' env' Nothing

    BoolToF p -> label' p i env Nothing -- noop

{-@ lazy labelStore' @-}
{-@ labelStore' :: assertion:(Assertion p) ->
                   m0:Nat -> Env p (Btwn 0 m0) ->
                   (m:{Int | m >= m0}, [LDSL p Int], Env p Int)
             <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
              \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
labelStore' :: (Num p, Ord p) => Assertion p -> Int -> Env p Int
            -> (Int, [LDSL p Int], Env p Int)
labelStore' assertion nextIndex env = let i = nextIndex in case assertion of
    DEF s d τ -> (i', [d'], add (VAR s τ, outputWire d') env')
      where (i', [d'], env') = label' d i env Nothing
    NZERO p1  -> (w'+1, [LNZERO p1' w'], env')
      where (w', [p1'], env') = label' p1 i env Nothing
    BOOL p1  -> (i', [LBOOL p1'], env')
      where (i', [p1'], env') = label' p1 i env Nothing
    EQA p1 p2 -> case M.lookup p1 env of
      Just i1 -> case M.lookup p2 env of
        Just i2 -> (i, [LEQA (LWIRE i1) (LWIRE i2)], env) -- both present
        Nothing -> (i', [p2'], env')
          where (i', [p2'], env') = label' p2 i env (Just i1) -- use i1 for p2
      Nothing -> case M.lookup p2 env of
        Just i2 -> (i', [p1'], env')
          where (i', [p1'], env') = label' p1 i env (Just i2) -- use i2 for p1
        Nothing -> (i'', [p1', p2'], env'')
          where (i', [p1'], env') = label' p1 i  env  Nothing
                i1 = outputWire p1'
                (i'', [p2'], env'') = label' p2 i' env' (Just i1)



{-@ withOutputWire :: m0:Nat -> requested:Maybe (Btwn 0 m0)
                   -> program:TypedDSL p
                   -> program':({v:Nat | v <= m0} -> LDSL p {v:Nat | v <= m0})
                   -> Env p (Btwn 0 m0)
                   -> (m:{Int | m >= m0}, [LDSL p Int], Env p Int)
                <\m   -> {l:[LDSL p (Btwn 0 m)] | len l = 1},
                 \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
withOutputWire :: Ord p => Int -> Maybe Int
               -> DSL p -> (Int -> LDSL p Int) -> Env p Int
               -> (Int, [LDSL p Int], Env p Int)
withOutputWire i requested program program' env = case requested of
  Just j  -> (i,   [program' j], add (program,j) env) -- use requested index
  Nothing -> (i+1, [program' i], add (program,i) env) -- use the next available
