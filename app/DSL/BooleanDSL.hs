{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module DSL.BooleanDSL
  ( BoolDSL(..)
  , BoolValue(..)
  , BoolExpr(..)
  , booleanSymbolicEnv
  , booleanConcreteEnv
  , prettyBoolExpr
  , normalizeBoolExpr
  , maxBoolVar
  , boolExprToHaskell
  , boolExprToPython
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

data BoolValue
  = VBool Bool
  | VExpr BoolExpr
  deriving (Eq, Show)

data BoolExpr
  = BVar Int
  | BConst Bool
  | BAnd BoolExpr BoolExpr
  | BOr BoolExpr BoolExpr
  | BNot BoolExpr
  deriving (Eq, Show, Ord)

prettyBoolExpr :: BoolExpr -> String
prettyBoolExpr (BVar i) = "x" ++ show i
prettyBoolExpr (BConst True) = "1"
prettyBoolExpr (BConst False) = "0"
prettyBoolExpr (BAnd a b) = "(" ++ prettyBoolExpr a ++ " AND " ++ prettyBoolExpr b ++ ")"
prettyBoolExpr (BOr a b) = "(" ++ prettyBoolExpr a ++ " OR " ++ prettyBoolExpr b ++ ")"
prettyBoolExpr (BNot a) = "NOT " ++ prettyBoolExpr a

-- =====================================================
-- DSL MONAD
-- =====================================================

newtype BoolDSL a = BoolDSL { unBoolDSL :: StandardDSL a }
    deriving (Functor, Applicative, Monad, MonadError String)

instance DSLMonad BoolDSL where
    type DSLValue BoolDSL = BoolValue
    runDSL (BoolDSL m) = runStandardDSL m
    liftError e = BoolDSL (throwError e)

instance DSLInterpreter BoolDSL where
    makeEnv = booleanSymbolicEnv
    makeEnvWithInputs = booleanConcreteEnv

-- =====================================================
-- OPERATIONS
-- =====================================================

-- Symbolic operations
opAndSymbolic :: [BoolValue] -> BoolDSL [BoolValue]
opAndSymbolic [VExpr a, VExpr b] = return [VExpr (BAnd a b)]
opAndSymbolic _ = liftError "AND: type mismatch"

opOrSymbolic :: [BoolValue] -> BoolDSL [BoolValue]
opOrSymbolic [VExpr a, VExpr b] = return [VExpr (BOr a b)]
opOrSymbolic _ = liftError "OR: type mismatch"

opNotSymbolic :: [BoolValue] -> BoolDSL [BoolValue]
opNotSymbolic [VExpr a] = return [VExpr (BNot a)]
opNotSymbolic _ = liftError "NOT: type mismatch"

opTrueSymbolic :: [BoolValue] -> BoolDSL [BoolValue]
opTrueSymbolic [] = return [VExpr (BConst True)]
opTrueSymbolic _ = liftError "TRUE: arity mismatch"

opFalseSymbolic :: [BoolValue] -> BoolDSL [BoolValue]
opFalseSymbolic [] = return [VExpr (BConst False)]
opFalseSymbolic _ = liftError "FALSE: arity mismatch"

-- Concrete operations
opAndConcrete :: [BoolValue] -> BoolDSL [BoolValue]
opAndConcrete [VBool a, VBool b] = return [VBool (a && b)]
opAndConcrete _ = liftError "AND: type mismatch"

opOrConcrete :: [BoolValue] -> BoolDSL [BoolValue]
opOrConcrete [VBool a, VBool b] = return [VBool (a || b)]
opOrConcrete _ = liftError "OR: type mismatch"

opNotConcrete :: [BoolValue] -> BoolDSL [BoolValue]
opNotConcrete [VBool a] = return [VBool (not a)]
opNotConcrete _ = liftError "NOT: type mismatch"

opTrue :: [BoolValue] -> BoolDSL [BoolValue]
opTrue [] = return [VBool True]
opTrue _ = liftError "TRUE: arity mismatch"

opFalse :: [BoolValue] -> BoolDSL [BoolValue]
opFalse [] = return [VBool False]
opFalse _ = liftError "FALSE: arity mismatch"

-- Structural operations
opCopy :: [BoolValue] -> BoolDSL [BoolValue]
opCopy [x] = return [x, x]
opCopy _ = liftError "COPY: arity mismatch"

opDiscard :: [BoolValue] -> BoolDSL [BoolValue]
opDiscard [_] = return []
opDiscard _ = liftError "DISCARD: arity mismatch"

opSwap :: [BoolValue] -> BoolDSL [BoolValue]
opSwap [a, b] = return [b, a]
opSwap _ = liftError "SWAP: arity mismatch"

opEquals :: [BoolValue] -> BoolDSL [BoolValue]
opEquals [VBool a, VBool b] = return [VBool (a == b)]
opEquals _ = liftError "EQUALS: requires two concrete Boolean values"
-- =====================================================
-- ENVIRONMENT CONSTRUCTION
-- =====================================================

booleanSymbolicEnv :: Int -> Env BoolDSL BoolValue
booleanSymbolicEnv n = loadOps symbolicOps baseEnv
  where
    baseEnv = emptyEnv
        { varMapping = Map.fromList [(Var i, VExpr (BVar i)) | i <- [0..n-1]] }

symbolicOps :: [((Char, String), [BoolValue] -> BoolDSL [BoolValue])]
symbolicOps =
    [ (('a', ""), opAndSymbolic)
    , (('o', ""), opOrSymbolic)
    , (('n', ""), opNotSymbolic)
    , (('c', "2"), opCopy)
    , (('d', "2"), opDiscard)
    , (('1', ""), opTrueSymbolic)
    , (('0', ""), opFalseSymbolic)
    , (('x', "1"), opSwap)
    , (('e', ""), opEquals)
    , (('e', "2"), opEquals)
    ]

booleanConcreteEnv :: [BoolValue] -> Env BoolDSL BoolValue
booleanConcreteEnv vals = loadOps concreteOps baseEnv
  where
    baseEnv = emptyEnv
        { varMapping = Map.fromList [(Var i, v) | (i, v) <- zip [0..] vals] }

concreteOps :: [((Char, String), [BoolValue] -> BoolDSL [BoolValue])]
concreteOps =
    [ (('a', ""), opAndConcrete)
    , (('o', ""), opOrConcrete)
    , (('n', ""), opNotConcrete)
    , (('c', "2"), opCopy)
    , (('d', "2"), opDiscard)
    , (('1', ""), opTrue)
    , (('0', ""), opFalse)
    , (('x', "1"), opSwap)
    , (('e', ""), opEquals)
    , (('e', "2"), opEquals)
    ]

-- =====================================================
-- NORMALIZATION & HELPERS
-- =====================================================

normalizeBoolExpr :: BoolExpr -> BoolExpr
normalizeBoolExpr (BVar i) = BVar i
normalizeBoolExpr (BConst b) = BConst b
normalizeBoolExpr (BNot (BNot e)) = normalizeBoolExpr e
normalizeBoolExpr (BNot e) = BNot (normalizeBoolExpr e)
normalizeBoolExpr (BAnd a b) = 
    let a' = normalizeBoolExpr a
        b' = normalizeBoolExpr b
    in case (a', b') of
        (BConst False, _) -> BConst False
        (_, BConst False) -> BConst False
        (BConst True, x) -> x
        (x, BConst True) -> x
        _ -> BAnd a' b'
normalizeBoolExpr (BOr a b) = 
    let a' = normalizeBoolExpr a
        b' = normalizeBoolExpr b
    in case (a', b') of
        (BConst True, _) -> BConst True
        (_, BConst True) -> BConst True
        (BConst False, x) -> x
        (x, BConst False) -> x
        _ -> BOr a' b'

maxBoolVar :: [BoolExpr] -> Int
maxBoolVar = maximum . (0:) . concatMap getVars
  where
    getVars (BVar i) = [i]
    getVars (BAnd a b) = getVars a ++ getVars b
    getVars (BOr a b) = getVars a ++ getVars b
    getVars (BNot a) = getVars a
    getVars _ = []

-- Code generation helpers
boolExprToHaskell :: BoolExpr -> String
boolExprToHaskell (BVar i) = "x" ++ show i
boolExprToHaskell (BConst True) = "True"
boolExprToHaskell (BConst False) = "False"
boolExprToHaskell (BAnd a b) = "(" ++ boolExprToHaskell a ++ " && " ++ boolExprToHaskell b ++ ")"
boolExprToHaskell (BOr a b) = "(" ++ boolExprToHaskell a ++ " || " ++ boolExprToHaskell b ++ ")"
boolExprToHaskell (BNot a) = "(not " ++ boolExprToHaskell a ++ ")"

boolExprToPython :: BoolExpr -> String
boolExprToPython (BVar i) = "x" ++ show i
boolExprToPython (BConst True) = "True"
boolExprToPython (BConst False) = "False"
boolExprToPython (BAnd a b) = "(" ++ boolExprToPython a ++ " and " ++ boolExprToPython b ++ ")"
boolExprToPython (BOr a b) = "(" ++ boolExprToPython a ++ " or " ++ boolExprToPython b ++ ")"
boolExprToPython (BNot a) = "(not " ++ boolExprToPython a ++ ")"