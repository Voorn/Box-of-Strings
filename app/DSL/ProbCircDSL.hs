{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module DSL.ProbCircDSL
  ( ProbCircDSL(..)
  , ProbCircValue(..)
  , opBernoulli
  , opAnd
  , opOr
  , opNot
  , opCopy
  , opDiscard
  , opSwap
  , probCircEnv
  , probCircEnvWithInputs
  , toSymbolic
  , prettyExpr
  ) where

import DSL.DSLClass
import DSL.ProbabilisticMonad
import SemanticInterpreterPoly
import qualified Data.Map as Map
import SemanticFree (Var(..), Semantic, Bundle, CompositeLibrary)
import Control.Monad.Except



-- =====================================================
-- VALUES AND EXPRESSIONS
-- =====================================================

data ProbCircValue
  = PVConst Bool
  | PVVar Int
  deriving (Eq, Show, Ord)

data ProbCircExpr
  = EVar Int
  | EConst Bool
  | EBernoulli Prob
  | EAnd ProbCircExpr ProbCircExpr
  | EOr ProbCircExpr ProbCircExpr
  | ENot ProbCircExpr
  deriving (Eq, Show, Ord)

toSymbolic :: ProbCircValue -> ProbCircExpr
toSymbolic (PVConst b) = EConst b
toSymbolic (PVVar i) = EVar i

prettyExpr :: ProbCircExpr -> String
prettyExpr (EVar i) = "x" ++ show i
prettyExpr (EConst True) = "1"
prettyExpr (EConst False) = "0"
prettyExpr (EBernoulli p) = "B(" ++ show p ++ ")"
prettyExpr (EAnd a b) = "(" ++ prettyExpr a ++ " AND " ++ prettyExpr b ++ ")"
prettyExpr (EOr a b) = "(" ++ prettyExpr a ++ " OR " ++ prettyExpr b ++ ")"
prettyExpr (ENot a) = "NOT " ++ prettyExpr a

-- =====================================================
-- DSL MONAD
-- =====================================================

newtype ProbCircDSL a = ProbCircDSL { unProbCircDSL :: ProbDSL a }
  deriving (Functor, Applicative, Monad, MonadError String)

instance DSLMonad ProbCircDSL where
  type DSLValue ProbCircDSL = ProbCircValue
  runDSL (ProbCircDSL m) = 
    case unDist (runExceptT (unProbDSL m)) of
      [(Right x, _)] -> Right x
      [(Left e, _)]  -> Left e
      _ -> Left "Non-deterministic result"
  liftError e = ProbCircDSL (throwError e)

instance DSLInterpreter ProbCircDSL where
  makeEnv = probCircEnv
  makeEnvWithInputs vals = (probCircEnv (length vals)) 
    { varMapping = Map.fromList [(Var i, v) | (i, v) <- zip [0..] vals] }

-- =====================================================
-- OPERATIONS
-- =====================================================

opBernoulli :: Prob -> [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opBernoulli p [] = do
  sample <- ProbCircDSL (liftDist (bernoulli p))
  return [PVConst sample]
opBernoulli _ _ = liftError "BERNOULLI: expects no inputs"

opAnd :: [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opAnd [PVConst a, PVConst b] = return [PVConst (a && b)]
opAnd _ = liftError "AND: requires concrete Boolean values"

opOr :: [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opOr [PVConst a, PVConst b] = return [PVConst (a || b)]
opOr _ = liftError "OR: requires concrete Boolean values"

opNot :: [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opNot [PVConst a] = return [PVConst (not a)]
opNot _ = liftError "NOT: requires concrete Boolean value"

opCopy :: [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opCopy [x] = return [x, x]
opCopy _ = liftError "COPY: expects 1 input"

opDiscard :: [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opDiscard [_] = return []
opDiscard _ = liftError "DISCARD: expects 1 input"

opSwap :: [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opSwap [a, b] = return [b, a]
opSwap _ = liftError "SWAP: expects 2 inputs"

opTrue :: [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opTrue [] = return [PVConst True]
opTrue _ = liftError "TRUE: arity mismatch"

opFalse :: [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opFalse [] = return [PVConst False]
opFalse _ = liftError "FALSE: arity mismatch"

opEquals :: [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opEquals [PVConst a, PVConst b] = return [PVConst (a == b)]
opEquals _ = liftError "EQUALS: requires two concrete Boolean values"

opCondit :: [ProbCircValue] -> ProbCircDSL [ProbCircValue]
opCondit [PVConst a , PVConst b] 
    |   a == b = ProbCircDSL (liftDist (Dist [([PVConst a] , 1)]))
    |   otherwise = ProbCircDSL  (liftDist (Dist []))
opCondit _ = liftError "Condit: crazy"

-- =====================================================
-- ENVIRONMENT
-- =====================================================

probCircEnv :: Int -> Env ProbCircDSL ProbCircValue
probCircEnv n = loadOps operations baseEnv
  where
    baseEnv = emptyEnv
      { varMapping = Map.fromList [(Var i, PVVar i) | i <- [0..max 0 (n-1)]] }
    operations =
      [ (('b', ""), opBernoulli 0.5)
      , (('a', ""), opAnd)
      , (('o', ""), opOr)
      , (('n', ""), opNot)
      , (('c', "2"), opCopy)
      , (('d', "2"), opDiscard)
      , (('x', "1"), opSwap)
      , (('1', ""), opTrue)
      , (('0', ""), opFalse)
      , (('e', ""), opCondit)
      , (('e', "2"), opCondit)
      , (('?', ""), opBernoulli 0.5)
      ]

probCircEnvWithInputs :: [ProbCircValue] -> Env ProbCircDSL ProbCircValue
probCircEnvWithInputs vals = loadOps operations baseEnv
  where
    baseEnv = emptyEnv
      { varMapping = Map.fromList [(Var i, v) | (i, v) <- zip [0..] vals] }
    operations =
      [ (('b', ""), opBernoulli 0.5)
      , (('a', ""), opAnd)
      , (('o', ""), opOr)
      , (('n', ""), opNot)
      , (('c', "2"), opCopy)
      , (('d', "2"), opDiscard)
      , (('x', "1"), opSwap)
      , (('1', ""), opTrue)
      , (('0', ""), opFalse)
      , (('e', ""), opCondit)
      , (('e', "2"), opCondit)
      , (('?', ""), opBernoulli 0.5)
      ]

-- =====================================================
-- EVALUATION
-- =====================================================

evalProbCirc :: CompositeLibrary 
             -> Semantic Bundle 
             -> [Bool]
             -> Dist (Either String [Bool])
evalProbCirc lib sem inputs = do
  let vals = map PVConst inputs
      env = probCircEnvWithInputs vals
      envWithComp = env { composites = lib }
      computation = runSemantic envWithComp sem
  
  result <- runExceptT (unProbDSL (unProbCircDSL computation))
  
  case result of
    Left err -> return (Left err)
    Right (resultVars, finalEnv) -> do
      let outputs = map (\v -> Map.findWithDefault (PVConst False) v (varMapping finalEnv)) resultVars
      let bools = map extractBool outputs
      return (Right bools)
  where
    extractBool (PVConst b) = b
    extractBool (PVVar _) = error "Cannot extract symbolic variable"

prettyDist :: (Show a, Ord a) => Dist a -> String
prettyDist = show . squishDist