{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module DSL.ArithmeticDSL
  ( ArithDSL(..)
  , ArithValue(..)
  , ArithExpr(..)
  , arithmeticSymbolicEnv
  , arithmeticConcreteEnv
  , prettyArithExpr
  , normalizeArithExpr
  , maxArithVar
  , arithExprToHaskell
  , arithExprToPython
  ) where

import DSL.DSLClass
import DSL.StandardMonad
import SemanticInterpreterPoly
import Control.Monad.Except
import qualified Data.Map as Map
import SemanticFree (Var(..), Semantic, Bundle, CompositeLibrary)

-- =====================================================
-- VALUE TYPES
-- =====================================================

data ArithValue
  = VInt Int
  | VExpr ArithExpr
  deriving (Eq, Show)

data ArithExpr
  = AVar Int
  | AConst Int
  | AAdd ArithExpr ArithExpr
  | AMul ArithExpr ArithExpr
  | ANeg ArithExpr
  deriving (Eq, Show, Ord)

prettyArithExpr :: ArithExpr -> String
prettyArithExpr (AVar i) = "x" ++ show i
prettyArithExpr (AConst n) = show n
prettyArithExpr (AAdd a b) = "(" ++ prettyArithExpr a ++ " + " ++ prettyArithExpr b ++ ")"
prettyArithExpr (AMul a b) = "(" ++ prettyArithExpr a ++ " * " ++ prettyArithExpr b ++ ")"
prettyArithExpr (ANeg a) = "(-" ++ prettyArithExpr a ++ ")"

-- =====================================================
-- DSL MONAD
-- =====================================================

newtype ArithDSL a = ArithDSL { unArithDSL :: StandardDSL a }
    deriving (Functor, Applicative, Monad, MonadError String)

instance DSLMonad ArithDSL where
    type DSLValue ArithDSL = ArithValue
    runDSL (ArithDSL m) = runStandardDSL m
    liftError e = ArithDSL (throwError e)

instance DSLInterpreter ArithDSL where
    makeEnv = arithmeticSymbolicEnv
    makeEnvWithInputs = arithmeticConcreteEnv

-- =====================================================
-- OPERATIONS
-- =====================================================

-- Symbolic operations
opAddSymbolic :: [ArithValue] -> ArithDSL [ArithValue]
opAddSymbolic [VExpr a, VExpr b] = return [VExpr (AAdd a b)]
opAddSymbolic _ = liftError "ADD: type mismatch"

opMulSymbolic :: [ArithValue] -> ArithDSL [ArithValue]
opMulSymbolic [VExpr a, VExpr b] = return [VExpr (AMul a b)]
opMulSymbolic _ = liftError "MUL: type mismatch"

opNegSymbolic :: [ArithValue] -> ArithDSL [ArithValue]
opNegSymbolic [VExpr a] = return [VExpr (ANeg a)]
opNegSymbolic _ = liftError "NEG: type mismatch"

-- Concrete operations
opAddConcrete :: [ArithValue] -> ArithDSL [ArithValue]
opAddConcrete [VInt a, VInt b] = return [VInt (a + b)]
opAddConcrete _ = liftError "ADD: type mismatch"

opMulConcrete :: [ArithValue] -> ArithDSL [ArithValue]
opMulConcrete [VInt a, VInt b] = return [VInt (a * b)]
opMulConcrete _ = liftError "MUL: type mismatch"

opNegConcrete :: [ArithValue] -> ArithDSL [ArithValue]
opNegConcrete [VInt a] = return [VInt (-a)]
opNegConcrete _ = liftError "NEG: type mismatch"

-- Structural operations
opCopy :: [ArithValue] -> ArithDSL [ArithValue]
opCopy [x] = return [x, x]
opCopy _ = liftError "COPY: arity mismatch"

opDiscard :: [ArithValue] -> ArithDSL [ArithValue]
opDiscard [_] = return []
opDiscard _ = liftError "DISCARD: arity mismatch"

opSwap :: [ArithValue] -> ArithDSL [ArithValue]
opSwap [a, b] = return [b, a]
opSwap _ = liftError "SWAP: arity mismatch"

-- =====================================================
-- ENVIRONMENT CONSTRUCTION
-- =====================================================

arithmeticSymbolicEnv :: Int -> Env ArithDSL ArithValue
arithmeticSymbolicEnv n = loadOps symbolicOps baseEnv
  where
    baseEnv = emptyEnv
        { varMapping = Map.fromList [(Var i, VExpr (AVar i)) | i <- [0..n-1]] }

symbolicOps :: [((Char, String), [ArithValue] -> ArithDSL [ArithValue])]
symbolicOps =
    [ (('a', ""), opAddSymbolic)
    , (('m', ""), opMulSymbolic)
    , (('n', ""), opNegSymbolic)
    , (('c', "2"), opCopy)
    , (('d', "2"), opDiscard)
    , (('x', "1"), opSwap)
    ]

arithmeticConcreteEnv :: [ArithValue] -> Env ArithDSL ArithValue
arithmeticConcreteEnv vals = loadOps concreteOps baseEnv
  where
    baseEnv = emptyEnv
        { varMapping = Map.fromList [(Var i, v) | (i, v) <- zip [0..] vals] }

concreteOps :: [((Char, String), [ArithValue] -> ArithDSL [ArithValue])]
concreteOps =
    [ (('a', ""), opAddConcrete)
    , (('m', ""), opMulConcrete)
    , (('n', ""), opNegConcrete)
    , (('c', "2"), opCopy)
    , (('d', "2"), opDiscard)
    , (('x', "1"), opSwap)
    ]

-- =====================================================
-- NORMALIZATION & HELPERS
-- =====================================================

normalizeArithExpr :: ArithExpr -> ArithExpr
normalizeArithExpr (AVar i) = AVar i
normalizeArithExpr (AConst n) = AConst n
normalizeArithExpr (ANeg (ANeg e)) = normalizeArithExpr e
normalizeArithExpr (ANeg e) = ANeg (normalizeArithExpr e)
normalizeArithExpr (AAdd a b) = 
    let a' = normalizeArithExpr a
        b' = normalizeArithExpr b
    in case (a', b') of
        (AConst 0, x) -> x
        (x, AConst 0) -> x
        (AConst m, AConst n) -> AConst (m + n)
        _ -> AAdd a' b'
normalizeArithExpr (AMul a b) = 
    let a' = normalizeArithExpr a
        b' = normalizeArithExpr b
    in case (a', b') of
        (AConst 0, _) -> AConst 0
        (_, AConst 0) -> AConst 0
        (AConst 1, x) -> x
        (x, AConst 1) -> x
        (AConst m, AConst n) -> AConst (m * n)
        _ -> AMul a' b'

maxArithVar :: [ArithExpr] -> Int
maxArithVar = maximum . (0:) . concatMap getVars
  where
    getVars (AVar i) = [i]
    getVars (AAdd a b) = getVars a ++ getVars b
    getVars (AMul a b) = getVars a ++ getVars b
    getVars (ANeg a) = getVars a
    getVars _ = []

-- Code generation helpers
arithExprToHaskell :: ArithExpr -> String
arithExprToHaskell (AVar i) = "x" ++ show i
arithExprToHaskell (AConst n) = show n
arithExprToHaskell (AAdd a b) = "(" ++ arithExprToHaskell a ++ " + " ++ arithExprToHaskell b ++ ")"
arithExprToHaskell (AMul a b) = "(" ++ arithExprToHaskell a ++ " * " ++ arithExprToHaskell b ++ ")"
arithExprToHaskell (ANeg a) = "(-" ++ arithExprToHaskell a ++ ")"

arithExprToPython :: ArithExpr -> String
arithExprToPython (AVar i) = "x" ++ show i
arithExprToPython (AConst n) = show n
arithExprToPython (AAdd a b) = "(" ++ arithExprToPython a ++ " + " ++ arithExprToPython b ++ ")"
arithExprToPython (AMul a b) = "(" ++ arithExprToPython a ++ " * " ++ arithExprToPython b ++ ")"
arithExprToPython (ANeg a) = "(-" ++ arithExprToPython a ++ ")"