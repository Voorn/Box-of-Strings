{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}

module SemanticInterpreterPoly
  ( Env(..)
  , emptyEnv
  , defineOp
  , loadOps
  , defineCompositeInEnv
  , runSemantic
  ) where

import SemanticFree
import Morph
import qualified Data.Map as Map
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)

-- =====================================================
-- ENVIRONMENT
-- =====================================================
data Env m v = Env
    { freshCounter :: Int
    , opFunctions  :: Map.Map (Char, String) ([v] -> m [v])
    , varMapping   :: Map.Map Var v
    , traceLog     :: [String]
    , composites   :: CompositeLibrary
    }

emptyEnv :: Env m v
emptyEnv = Env
  { freshCounter = 0
  , opFunctions  = Map.empty
  , varMapping   = Map.empty
  , traceLog     = []
  , composites   = Map.empty
  }

defineOp
  :: (Char, String)
  -> ([v] -> m [v])
  -> Env m v
  -> Env m v
defineOp key f env =
  env { opFunctions = Map.insert key f (opFunctions env) }

loadOps
  :: [((Char, String), [v] -> m [v])]
  -> Env m v
  -> Env m v
loadOps ops env =
  env { opFunctions = Map.fromList ops `Map.union` opFunctions env }

defineCompositeInEnv :: Char -> String -> Morph -> String -> Env m v -> Env m v
defineCompositeInEnv opChar opStyle morph dslName env =
    let name = [opChar] ++ opStyle
        lib = composites env
        newLib = defineComposite name morph dslName lib
    in env { composites = newLib }

addTrace :: String -> Env m v -> Env m v
addTrace msg env =
  env { traceLog = traceLog env ++ [msg] }

-- =====================================================
-- FULLY POLYMORPHIC INTERPRETER
-- =====================================================

runSemantic
  :: MonadError String m
  => Env m v
  -> Semantic Bundle
  -> m (Bundle, Env m v)

-- ------------------------------
-- Pure case
-- ------------------------------
runSemantic env (Pure bundle) =
  return (bundle, env)

-- ------------------------------
-- Fresh Variables
-- ------------------------------
runSemantic env (Free (FreshVarsF n k)) =
  let start = freshCounter env
      vars  = [Var i | i <- [start .. start + n - 1]]
      env'  = addTrace ("FreshVars " ++ show n ++ " => " ++ show vars)
             env { freshCounter = start + n }
  in runSemantic env' (k vars)

-- ------------------------------
-- Swap
-- ------------------------------
runSemantic env (Free (SwapF pos bundle k)) = do
  if pos + 1 >= length bundle
    then throwError "Swap: not enough variables"
    else do
      let before = take pos bundle
          v1 = bundle !! pos
          v2 = bundle !! (pos + 1)
          after = drop (pos + 2) bundle          
      let newBundle = before ++ [v2, v1] ++ after
          env' = addTrace ("Swap at pos " ++ show pos ++ ": " ++ show v1 ++ " <-> " ++ show v2) env      
      runSemantic env' (k newBundle)

-- ------------------------------
-- Copy
-- ------------------------------
runSemantic env (Free (CopyF pos var vars k)) = do
  if pos >= length vars
    then throwError "Copy: position out of bounds"
    else do
      let before = take pos vars
          after = drop (pos + 1) vars
      val <- lookupVar env var
      let start = freshCounter env
          newVar = Var start
          newMapping = Map.singleton newVar val
          newBundle = before ++ [var, newVar] ++ after
          env' = addTrace ("Copy at pos " ++ show pos)
                 env { freshCounter = start + 1
                     , varMapping = Map.union newMapping (varMapping env)
                     }
      runSemantic env' (k newBundle)

-- ------------------------------
-- Discard
-- ------------------------------
runSemantic env (Free (DiscardF pos vars k)) = do
  if pos >= length vars
    then throwError "Discard: position out of bounds"
    else do
      let var = vars !! pos
          before = take pos vars
          after = drop (pos + 1) vars
          newBundle = before ++ after
          env' = addTrace ("Discard at pos " ++ show pos) env
      runSemantic env' (k newBundle)

-- ------------------------------
-- Merge (co-copy / addition)
-- ------------------------------
runSemantic env (Free (MergeF pos vars k)) = do
  if pos + 1 >= length vars
    then throwError "Merge: not enough variables"
    else do
      let [a, b] = take 2 (drop pos vars)
          before = take pos vars
          after = drop (pos + 2) vars
      valA <- lookupVar env a
      valB <- lookupVar env b
      let newBundle = before ++ [a] ++ after
          env' = addTrace ("Merge at pos " ++ show pos ++ 
                          ": " ++ show [a, b] ++ " -> " ++ show [a]) env
      runSemantic env' (k newBundle)

-- ------------------------------
-- Create (co-unit / make unit element)
-- ------------------------------
runSemantic env (Free (CreateF pos vars k)) = do
  let before = take pos vars
      after = drop pos vars
      start = freshCounter env
      newVar = Var start
      newBundle = before ++ [newVar] ++ after
      env' = addTrace ("Create at pos " ++ show pos) 
             env { freshCounter = start + 1 }
  runSemantic env' (k newBundle)

-- ------------------------------
-- Apply Operation
-- ------------------------------
runSemantic env (Free (ApplyOpF c s pos inAr outAr vars k)) = do
  let funcKey = (c, s)
      compositeName = [c] ++ s
  
  case lookupComposite compositeName (composites env) of
    Just comp -> do
      let before = take pos vars
          inputs = take inAr (drop pos vars)
          after = drop (pos + inAr) vars      
      inputVals <- mapM (lookupVar env) inputs      
      let innerEnv = env 
            { varMapping = Map.fromList [(Var i, val) | (i, val) <- zip [0..] inputVals]
            , freshCounter = 0
            }          
          innerSem = morphToSemantic (composMorph comp)      
      (innerResults, innerFinalEnv) <- runSemantic innerEnv innerSem
      outputVals <- mapM (lookupVar innerFinalEnv) innerResults      
      let outerStart = freshCounter env
          outputVars = [Var i | i <- [outerStart .. outerStart + outAr - 1]]
          newMapping = Map.fromList (zip outputVars outputVals)
          resultBundle = before ++ outputVars ++ after
          env' = addTrace ("Composite '" ++ compositeName ++ "' at pos " ++ show pos)
                 env { freshCounter = outerStart + outAr
                     , varMapping = Map.union newMapping (varMapping env)
                     }
      runSemantic env' (k resultBundle)
    Nothing -> do
      case Map.lookup funcKey (opFunctions env) of
        Nothing ->
          throwError $ "Undefined operation: '" ++ [c] ++ s ++ "'"
        Just f -> do
          let inputs = take inAr (drop pos vars)
          values <- mapM (lookupVar env) inputs
          outputs <- f values
          let start = freshCounter env
              newVars = [Var i | i <- [start .. start + outAr - 1]]
              newMapping = Map.fromList (zip newVars outputs)
              resultBundle =
                  take pos vars
               ++ newVars
               ++ drop (pos + inAr) vars
              env' =
                addTrace ("ApplyOp '" ++ [c] ++ s ++ "' at pos "
                          ++ show pos)
                env { freshCounter = start + outAr
                    , varMapping = Map.union newMapping (varMapping env)
                    }
          runSemantic env' (k resultBundle)

-- ------------------------------
-- Apply Composition
-- ------------------------------
runSemantic env (Free (ApplyCompF _rew innerMorph pos vars k)) = do
  let (inAr, outAr) = typeMorph innerMorph      
      before = take pos vars
      inputs = take inAr (drop pos vars)
      after = drop (pos + inAr) vars
  inputVals <- mapM (lookupVar env) inputs
  
  let innerEnv = env 
        { varMapping = Map.fromList [(Var i, val) | (i, val) <- zip [0..] inputVals]
        , freshCounter = 0
        }
      
      innerSem = morphToSemantic innerMorph
  
  -- Run the inner morphism in its own context
  (innerResultVars, innerFinalEnv) <- runSemantic innerEnv innerSem
  
  -- Extract the output values from the inner context
  outputVals <- mapM (lookupVar innerFinalEnv) innerResultVars
  
  -- Create fresh variables in the outer context for the outputs
  let outerStart = freshCounter env
      outputVars = [Var i | i <- [outerStart .. outerStart + outAr - 1]]
      newMapping = Map.fromList (zip outputVars outputVals)
      resultBundle = before ++ outputVars ++ after      
      env' = addTrace ("ApplyComp at pos " ++ show pos)
             env { freshCounter = outerStart + outAr
                 , varMapping = Map.union newMapping (varMapping env)
                 }
  
  runSemantic env' (k resultBundle)

-- =====================================================
-- Helpers
-- =====================================================

lookupVar :: MonadError String m => Env m v -> Var -> m v
lookupVar env v =
  case Map.lookup v (varMapping env) of
    Just val -> return val
    Nothing  -> throwError $ "Uninitialized variable: " ++ show v