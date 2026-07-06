{-# LANGUAGE TypeFamilies #-}

module DSL.DSLClass
  ( DSLMonad(..)
  , DSLInterpreter(..)
  ) where

import SemanticFree (Semantic, Bundle)
import SemanticInterpreterPoly (Env)

-- =====================================================
-- DSL MONAD TYPE CLASS
-- =====================================================

class Monad m => DSLMonad m where
    type DSLValue m :: *
    runDSL :: m a -> Either String a    
    liftError :: String -> m a

-- =====================================================
-- DSL INTERPRETER TYPE CLASS
-- =====================================================

class DSLMonad m => DSLInterpreter m where
    makeEnv :: Int -> Env m (DSLValue m)
    makeEnvWithInputs :: [DSLValue m] -> Env m (DSLValue m)
    makeEnvWithInputs _ = makeEnv 0