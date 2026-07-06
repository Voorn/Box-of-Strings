module Equivalence
  ( checkBoolEquivalence
  , checkArithEquivalence
  , checkProbEquivalence
  , EquivalenceResult(..)
  , validateCurrentPage
  , validateTheoryFromPage
  ) where


import Morph (MR(..), Morph, Relat, typeMorph)
import Parse (Page, Theor)
import Theory
import SemanticFree
import Control.Monad (when)
import Evaluation
import qualified DSL.BooleanDSL as Bool
import qualified DSL.ArithmeticDSL as Arith
import qualified DSL.ProbCircDSL as Prob
import DSL.ProbabilisticMonad
import qualified Data.Map as Map


-- =====================================================
-- PAGE/THEORY VALIDATION
-- =====================================================

validateCurrentPage :: String -> CompositeLibrary -> Page -> IO ()
validateCurrentPage dslName lib page = do
  putStrLn "\n=== CHECKING PAGE EQUIVALENCE ==="
  let ((rel, m1, m2, w , name), _ , _ , _ , _ , _ , _) = page

  case rel of
    MEqual -> do
      let result = checkEquivalenceByDSL dslName lib m1 m2
      case result of
        Right Equivalent -> putStrLn "Morphisms are equivalent!"
        Right (NotEquivalent reason) -> putStrLn $ "Not equivalent: " ++ reason
        Right (CannotCheck reason) -> putStrLn $ "Cannot check: " ++ reason
        Left err -> putStrLn $ "Error: " ++ err


validateTheoryFromPage :: String -> CompositeLibrary -> Page -> IO ()
validateTheoryFromPage dslName lib page = do
  putStrLn "\n=== VALIDATING ALL THEORY RELATIONS ==="
  let (_, _ , (_, _, rels, _), _ , _, _ , _) = page
  let rels_select = getTheoryRelations rels
  
  results <- mapM (checkRelation dslName lib) rels_select
  
  let total = length results
      passed = length [() | Right Equivalent <- results]
      failed = length [() | Right (NotEquivalent _) <- results]
      errors = length [() | Left _ <- results]
  
  putStrLn $ "\nSummary: " ++ show passed ++ "/" ++ show total ++ " passed"
  when (failed > 0) $ putStrLn $ "  " ++ show failed ++ " failed"
  when (errors > 0) $ putStrLn $ "  " ++ show errors ++ " errors"

checkRelation :: String -> CompositeLibrary -> (Morph, Morph) -> IO (Either String EquivalenceResult)
checkRelation dslName lib (m1, m2) = do
  let result = checkEquivalenceByDSL dslName lib m1 m2
  case result of
    Right Equivalent -> do
      putStrLn $ "  Equivalent"
      return result
    Right (NotEquivalent reason) -> do
      putStrLn $ "  Not equivalent: " ++ reason
      return result
    Right (CannotCheck reason) -> do
      putStrLn $ "  Cannot check: " ++ reason
      return result
    Left err -> do
      putStrLn $ "  Error: " ++ err
      return result

checkEquivalenceByDSL :: String -> CompositeLibrary -> Morph -> Morph -> Either String EquivalenceResult
checkEquivalenceByDSL "boolean" = checkBoolEquivalence
checkEquivalenceByDSL "arith" = checkArithEquivalence
checkEquivalenceByDSL "probcirc" = checkProbEquivalence
checkEquivalenceByDSL dsl = \_ _ _ -> Left $ "Unknown DSL: " ++ dsl

getTheoryRelations :: [Relat] -> [(Morph, Morph)]
getTheoryRelations rels = 
  [ (m1, m2) | (MEqual, m1, m2, _ , _) <- rels ]

-- =====================================================
-- EQUIVALENCE RESULTS
-- =====================================================

data EquivalenceResult
  = Equivalent
  | NotEquivalent String  
  | CannotCheck String    
  deriving (Eq, Show)

-- =====================================================
-- BOOLEAN EQUIVALENCE
-- =====================================================

checkBoolEquivalence :: CompositeLibrary -> Morph -> Morph -> Either String EquivalenceResult
checkBoolEquivalence lib m1 m2 = do
  let (in1, out1) = typeMorph m1
      (in2, out2) = typeMorph m2
  if (in1, out1) /= (in2, out2)
    then return $ CannotCheck "Type mismatch"
    else if in1 <= 10
      then checkBoolTruthTableEquiv lib m1 m2
      else checkBoolSymbolicEquiv lib m1 m2

checkBoolTruthTableEquiv :: CompositeLibrary -> Morph -> Morph -> Either String EquivalenceResult
checkBoolTruthTableEquiv lib m1 m2 = do
  result1 <- evaluateBool lib m1 TruthTable Nothing
  result2 <- evaluateBool lib m2 TruthTable Nothing
  
  case (result1, result2) of
    (BoolTableResult table1, BoolTableResult table2) ->
      case findMismatch table1 table2 of
        Nothing -> return Equivalent
        Just (input, out1, out2) -> 
          return $ NotEquivalent $ 
            "Counterexample: input " ++ show input ++ 
            " gives " ++ show out1 ++ " vs " ++ show out2
    _ -> return $ CannotCheck "Unexpected result type"
  where
    findMismatch [] [] = Nothing
    findMismatch ((inp, out1):rest1) ((_, out2):rest2)
      | out1 == out2 = findMismatch rest1 rest2
      | otherwise = Just (inp, out1, out2)
    findMismatch _ _ = Nothing

checkBoolSymbolicEquiv :: CompositeLibrary -> Morph -> Morph -> Either String EquivalenceResult
checkBoolSymbolicEquiv lib m1 m2 = do
  result1 <- evaluateBool lib m1 Symbolic Nothing
  result2 <- evaluateBool lib m2 Symbolic Nothing
  
  case (result1, result2) of
    (BoolExprResult exprs1, BoolExprResult exprs2) -> do
      let normalized1 = map Bool.normalizeBoolExpr exprs1
          normalized2 = map Bool.normalizeBoolExpr exprs2
      
      if normalized1 == normalized2
        then return Equivalent
        else return $ NotEquivalent "Symbolic expressions differ after normalization"
    _ -> return $ CannotCheck "Unexpected result type"

-- =====================================================
-- ARITHMETIC EQUIVALENCE
-- =====================================================

checkArithEquivalence :: CompositeLibrary -> Morph -> Morph -> Either String EquivalenceResult
checkArithEquivalence lib m1 m2 = do
  let (in1, out1) = typeMorph m1
      (in2, out2) = typeMorph m2
  if (in1, out1) /= (in2, out2)
    then return $ CannotCheck "Type mismatch"
    else do
      result1 <- evaluateArith lib m1 Symbolic Nothing
      result2 <- evaluateArith lib m2 Symbolic Nothing
      
      case (result1, result2) of
        (ArithExprResult exprs1, ArithExprResult exprs2) -> do
          let normalized1 = map Arith.normalizeArithExpr exprs1
              normalized2 = map Arith.normalizeArithExpr exprs2
          
          if normalized1 == normalized2
            then return Equivalent
            else return $ NotEquivalent "Arithmetic expressions differ after normalization"
        _ -> return $ CannotCheck "Unexpected result type"

-- =====================================================
-- PROBABILISTIC EQUIVALENCE
-- =====================================================

checkProbEquivalence :: CompositeLibrary -> Morph -> Morph -> Either String EquivalenceResult
checkProbEquivalence lib m1 m2 = do
  let (in1, out1) = typeMorph m1
      (in2, out2) = typeMorph m2
  if (in1, out1) /= (in2, out2)
    then return $ CannotCheck "Type mismatch"
    else do
      result1 <- evaluateProb lib m1 Distribution Nothing
      result2 <- evaluateProb lib m2 Distribution Nothing
      
      case (result1, result2) of
        (ProbDistResult dist1, ProbDistResult dist2) -> do
          let normalized1 = squishDist dist1
              normalized2 = squishDist dist2
          
          if compareDists normalized1 normalized2
            then return Equivalent
            else return $ NotEquivalent "Probability distributions differ"
        _ -> return $ CannotCheck "Unexpected result type"
  where
    compareDists (DSL.ProbabilisticMonad.Dist xs) (DSL.ProbabilisticMonad.Dist ys) =
      let m1 = Map.fromList xs
          m2 = Map.fromList ys
      in Map.keys m1 == Map.keys m2 &&
         all (\k -> abs (m1 Map.! k - m2 Map.! k) < 1e-9) (Map.keys m1)