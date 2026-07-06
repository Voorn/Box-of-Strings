module Evaluation
  ( EvalMode(..)
  , EvalResult(..)
  , evaluateBool
  , evaluateArith
  , evaluateProb
  , prettyResult
  , parseMode
  ,evaluateWithMode
  ) where

import DSL.DSLClass
import qualified DSL.BooleanDSL as Bool
import qualified DSL.ArithmeticDSL as Arith
import qualified DSL.ProbCircDSL as Prob
import DSL.ProbabilisticMonad
import SemanticInterpreterPoly
import SemanticFree
import Morph
import qualified Data.Map as Map
import Text.Printf (printf)

-- =====================================================
-- EVALUATION MODES AND RESULTS
-- =====================================================

data EvalMode
  = Concrete        
  | Symbolic        
  | TruthTable      
  | Distribution   
  deriving (Eq, Show)

data EvalResult
  = BoolResult [Bool]
  | BoolExprResult [Bool.BoolExpr]
  | BoolTableResult [(InputRow, [Bool])]
  | ArithResult [Int]
  | ArithExprResult [Arith.ArithExpr]
  | ProbDistResult (Dist [Bool])
  | ProbTableResult [(InputRow, Dist [Bool])]
  | ErrorResult String
  deriving (Show)

type InputRow = [Bool]

data EvalModeDSL
    = BooleanMode
    | ArithmeticMode
    | ProbCircMode
    deriving (Eq, Show)

parseMode :: String -> Maybe EvalModeDSL
parseMode "boolean" = Just BooleanMode
parseMode "arith" = Just ArithmeticMode
parseMode "probcirc" = Just ProbCircMode
parseMode _ = Nothing

-- =====================================================
-- UNIFIED EVALUATION WITH MODE
-- =====================================================

evaluateWithMode :: EvalModeDSL -> CompositeLibrary -> Morph -> IO ()
evaluateWithMode BooleanMode lib morph = do
  putStrLn "\n=== BOOLEAN DSL EVALUATION ==="
  
  putStrLn "\n--- Concrete Evaluation ---"
  runAndPrint $ evaluateBool lib morph Concrete Nothing
  
  putStrLn "\n--- Symbolic Evaluation ---"
  runAndPrint $ evaluateBool lib morph Symbolic Nothing
  
  putStrLn "\n--- Truth Table ---"
  runAndPrint $ evaluateBool lib morph TruthTable Nothing

evaluateWithMode ArithmeticMode lib morph = do
  putStrLn "\n=== ARITHMETIC DSL EVALUATION ==="
  
  putStrLn "\n--- Concrete Evaluation ---"
  runAndPrint $ evaluateArith lib morph Concrete Nothing
  
  putStrLn "\n--- Symbolic Evaluation ---"
  runAndPrint $ evaluateArith lib morph Symbolic Nothing

evaluateWithMode ProbCircMode lib morph = do
  putStrLn "\n=== PROBABILISTIC DSL EVALUATION ==="
  
  let (inAr, _) = typeMorph morph
  
  if inAr > 0 then do
    putStrLn "\n--- Hybrid Truth Table (Deterministic Inputs x Probabilistic Sources) ---"
    runAndPrint $ evaluateProb lib morph TruthTable Nothing
  else do
    putStrLn "\n--- Distribution (No Deterministic Inputs) ---"
    runAndPrint $ evaluateProb lib morph Distribution Nothing
  
  putStrLn "\n--- Concrete Sample ---"
  runAndPrint $ evaluateProb lib morph Concrete Nothing

runAndPrint :: Either String EvalResult -> IO ()
runAndPrint (Left err) = putStrLn $ "Error: " ++ err
runAndPrint (Right result) = putStrLn $ prettyResult result


-- =====================================================
-- BOOLEAN EVALUATION
-- =====================================================

evaluateBool :: CompositeLibrary -> Morph -> EvalMode -> Maybe [Bool] -> Either String EvalResult
evaluateBool lib morph mode maybeInputs = case mode of
  Concrete -> case maybeInputs of
    Just inputs -> evalBoolConcreteWith lib morph inputs
    Nothing -> do
      let (inAr, _) = typeMorph morph
      evalBoolConcreteWith lib morph (replicate inAr False)
  
  Symbolic -> evalBoolSymbolic lib morph
  
  TruthTable -> evalBoolTruthTable lib morph
  
  _ -> Left "Invalid evaluation mode for Boolean DSL"

evalBoolConcreteWith :: CompositeLibrary -> Morph -> [Bool] -> Either String EvalResult
evalBoolConcreteWith lib morph inputs = do
  let sem = morphToSemantic morph
      vals = map Bool.VBool inputs
      env = Bool.booleanConcreteEnv vals
      envWithComp = env { composites = lib }
  (resultVars, finalEnv) <- runDSL (runSemantic envWithComp sem)
  let results = map (\v -> extractBool $ Map.findWithDefault (Bool.VBool False) v (varMapping finalEnv)) resultVars
  return $ BoolResult results
  where
    extractBool (Bool.VBool b) = b
    extractBool _ = error "Type error: expected VBool"

evalBoolSymbolic :: CompositeLibrary -> Morph -> Either String EvalResult
evalBoolSymbolic lib morph = do
  let (inAr, _) = typeMorph morph
      sem = morphToSemantic morph
      env = Bool.booleanSymbolicEnv inAr
      envWithComp = env { composites = lib }
  (resultVars, finalEnv) <- runDSL (runSemantic envWithComp sem)
  let results = map (\v -> extractExpr $ Map.findWithDefault (Bool.VExpr (Bool.BVar 0)) v (varMapping finalEnv)) resultVars
  return $ BoolExprResult results
  where
    extractExpr (Bool.VExpr e) = e
    extractExpr _ = error "Type error: expected VExpr"

evalBoolTruthTable :: CompositeLibrary -> Morph -> Either String EvalResult
evalBoolTruthTable lib morph = do
  let (inAr, _) = typeMorph morph
      inputs = generateBoolInputs inAr
  results <- mapM (\inp -> evalBoolConcreteWith lib morph inp) inputs
  let rows = zipWith (\inp (BoolResult out) -> (inp, out)) inputs results
  return $ BoolTableResult rows

-- =====================================================
-- ARITHMETIC EVALUATION
-- =====================================================

evaluateArith :: CompositeLibrary -> Morph -> EvalMode -> Maybe [Int] -> Either String EvalResult
evaluateArith lib morph mode maybeInputs = case mode of
  Concrete -> case maybeInputs of
    Just inputs -> evalArithConcreteWith lib morph inputs
    Nothing -> do
      let (inAr, _) = typeMorph morph
      evalArithConcreteWith lib morph (replicate inAr 0)
  
  Symbolic -> evalArithSymbolic lib morph
  
  _ -> Left "Invalid evaluation mode for Arithmetic DSL"

evalArithConcreteWith :: CompositeLibrary -> Morph -> [Int] -> Either String EvalResult
evalArithConcreteWith lib morph inputs = do
  let sem = morphToSemantic morph
      vals = map Arith.VInt inputs
      env = Arith.arithmeticConcreteEnv vals
      envWithComp = env { composites = lib }
  (resultVars, finalEnv) <- runDSL (runSemantic envWithComp sem)
  let results = map (\v -> extractInt $ Map.findWithDefault (Arith.VInt 0) v (varMapping finalEnv)) resultVars
  return $ ArithResult results
  where
    extractInt (Arith.VInt i) = i
    extractInt _ = error "Type error: expected VInt"

evalArithSymbolic :: CompositeLibrary -> Morph -> Either String EvalResult
evalArithSymbolic lib morph = do
  let (inAr, _) = typeMorph morph
      sem = morphToSemantic morph
      env = Arith.arithmeticSymbolicEnv inAr
      envWithComp = env { composites = lib }
  (resultVars, finalEnv) <- runDSL (runSemantic envWithComp sem)
  let results = map (\v -> extractExpr $ Map.findWithDefault (Arith.VExpr (Arith.AVar 0)) v (varMapping finalEnv)) resultVars
  return $ ArithExprResult results
  where
    extractExpr (Arith.VExpr e) = e
    extractExpr _ = error "Type error: expected VExpr"

-- =====================================================
-- PROBABILISTIC EVALUATION
-- =====================================================

evaluateProb :: CompositeLibrary -> Morph -> EvalMode -> Maybe [Bool] -> Either String EvalResult
evaluateProb lib morph mode maybeInputs = case mode of
  Distribution -> evalProbDist lib morph maybeInputs
  Concrete -> evalProbConcrete lib morph maybeInputs
  TruthTable -> evalProbTruthTable lib morph
  _ -> Left "Invalid evaluation mode for Probabilistic DSL"

evalProbTruthTable :: CompositeLibrary -> Morph -> Either String EvalResult
evalProbTruthTable lib morph = do
  let (inAr, _) = typeMorph morph
  if inAr == 0
    then evalProbDist lib morph Nothing
    else do
      let allInputs = generateBoolInputs inAr
      results <- mapM (\inputs -> evalProbDistWith lib morph inputs) allInputs
      return $ ProbTableResult (zip allInputs results)

evalProbDistWith :: CompositeLibrary -> Morph -> [Bool] -> Either String (Dist [Bool])
evalProbDistWith lib morph inputs = do
  let sem = morphToSemantic morph
      vals = map Prob.PVConst inputs
      env = Prob.probCircEnvWithInputs vals
      envWithComp = env { composites = lib }
  let dist = runProbDSL (Prob.unProbCircDSL (runSemantic envWithComp sem))
  let resultDist = do
        result <- dist
        case result of
          Left err -> return (Left err)
          Right (resultVars, finalEnv) -> do
            let outputs = map (\v -> Map.findWithDefault (Prob.PVConst False) v (varMapping finalEnv)) resultVars
            return $ Right (map extractBool outputs)
  case unDist resultDist of
    [(Left err, _)] -> Left err
    _ -> return $ fmap (either (const []) id) resultDist
  where
    extractBool (Prob.PVConst b) = b
    extractBool _ = error "Type error: expected PVConst"

evalProbDist :: CompositeLibrary -> Morph -> Maybe [Bool] -> Either String EvalResult
evalProbDist lib morph maybeInputs = do
  let sem = morphToSemantic morph
      (inAr, _) = typeMorph morph
      inputs = case maybeInputs of
        Just vals -> vals
        Nothing -> replicate inAr False
      vals = map Prob.PVConst inputs
      env = if null inputs then Prob.probCircEnv 0 else Prob.probCircEnvWithInputs vals
      envWithComp = env { composites = lib }
  let dist = runProbDSL (Prob.unProbCircDSL (runSemantic envWithComp sem))
  let resultDist = do
        result <- dist
        case result of
          Left err -> return (Left err)
          Right (resultVars, finalEnv) -> do
            let outputs = map (\v -> Map.findWithDefault (Prob.PVConst False) v (varMapping finalEnv)) resultVars
            return $ Right (map extractBool outputs)
  case unDist resultDist of
    [(Left err, _)] -> Left err
    _ -> return $ ProbDistResult (fmap (either (const []) id) resultDist)
  where
    extractBool (Prob.PVConst b) = b
    extractBool _ = error "Type error: expected PVConst"

evalProbConcrete :: CompositeLibrary -> Morph -> Maybe [Bool] -> Either String EvalResult
evalProbConcrete lib morph maybeInputs = do
  dist <- case evalProbDist lib morph maybeInputs of
    Right (ProbDistResult d) -> Right d
    Right _ -> Left "Expected distribution result"
    Left err -> Left err
  case unDist dist of
    ((outcome, _):_) -> return $ BoolResult outcome
    [] -> Left "Empty distribution"

-- =====================================================
-- HELPERS
-- =====================================================

generateBoolInputs :: Int -> [[Bool]]
generateBoolInputs 0 = [[]]
generateBoolInputs n = [x:xs | x <- [False, True], xs <- generateBoolInputs (n-1)]

prettyResult :: EvalResult -> String
prettyResult (BoolResult bs) = show bs
prettyResult (BoolExprResult exprs) = unlines $ map Bool.prettyBoolExpr exprs
prettyResult (BoolTableResult rows) = 
  unlines [show inp ++ " -> " ++ show out | (inp, out) <- rows]
prettyResult (ArithResult is) = show is
prettyResult (ArithExprResult exprs) = unlines $ map Arith.prettyArithExpr exprs
prettyResult (ProbDistResult dist) = prettyDist dist
prettyResult (ProbTableResult rows) = prettyProbTable rows
prettyResult (ErrorResult err) = "Error: " ++ err

prettyDist :: Dist [Bool] -> String
prettyDist dist = unlines
  [ printf "%6.2f%% %s" (p * 100) (show outcome)
  | (outcome, p) <- unDist (squishDist dist)
  , p > 0.001
  ]

prettyProbTable :: [(InputRow, Dist [Bool])] -> String
prettyProbTable rows = unlines $ map prettyRow rows
  where
    prettyRow (inputs, dist) = 
      "Input: " ++ show inputs ++ "\n" ++ 
      indent (prettyDist dist)
    
    indent = unlines . map ("  " ++) . lines