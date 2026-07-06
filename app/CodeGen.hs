module CodeGen
  ( generateBoolCode
  , generateArithCode
  , generateProbCode
  , CodeTarget(..)
  , GeneratedCode(..)
  , generateFromMorph
  , fileExtension
  , defaultTarget
  ) where

import Evaluation
import DSL.BooleanDSL
import DSL.ProbabilisticMonad
import Data.List (intercalate)
import qualified DSL.BooleanDSL as Bool
import qualified DSL.ArithmeticDSL as Arith
import qualified DSL.ProbCircDSL as Prob
import SemanticFree
import Morph (Morph, typeMorph)
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad.State
import qualified Data.Map as Map
import SemanticFree (Semantic(..), SemanticF(..), Bundle, Var(..))

-- =====================================================
-- CODE GENERATION TYPES
-- =====================================================

data CodeTarget = Haskell | Python deriving (Eq, Show)

data GeneratedCode = GeneratedCode
  { codeTarget :: CodeTarget
  , codeSource :: String
  , codeDescription :: String
  } deriving (Show)

-- =====================================================
-- BOOLEAN CODE GENERATION
-- =====================================================

generateBoolCode :: CompositeLibrary -> Morph -> CodeTarget -> Either String GeneratedCode
generateBoolCode lib morph target = do
  result <- evaluateBool lib morph Symbolic Nothing
  case result of
    BoolExprResult exprs ->
      case target of
        Haskell -> return $ GeneratedCode Haskell (genHaskellBool exprs) "Boolean circuit"
        Python -> return $ GeneratedCode Python (genPythonBool exprs) "Boolean circuit"
    _ -> Left "Expected BoolExprResult"


genHaskellBool :: [Bool.BoolExpr] -> String
genHaskellBool exprs = unlines
  [ "module Main where"
  , ""
  , "-- Circuit function"
  , "circuit :: " ++ inputType ++ " -> " ++ outputType
  , "circuit " ++ pattern ++ " = " ++ outputExpr
  , ""
  , "-- Test with all input combinations"
  , "testAll :: [(" ++ inputType ++ ", " ++ outputType ++ ")]"
  , "testAll = [(inputs, circuit inputs) | inputs <- allInputs]"
  , "  where"
  , "    allInputs = " ++ generateAllInputs numInputs
  , ""
  , "main :: IO ()"
  , "main = do"
  , "    putStrLn \"Boolean Circuit:\""
  , "    mapM_ (\\(inp, out) -> putStrLn $ show inp ++ \" -> \" ++ show out) testAll"
  ]
  where
    numInputs = Bool.maxBoolVar exprs + 1
    inputType = tuplify $ replicate numInputs "Bool"
    outputType = tuplify $ replicate (length exprs) "Bool"
    pattern = tuplify ["x" ++ show i | i <- [0..numInputs-1]]
    outputExpr = tuplify [Bool.boolExprToHaskell e | e <- exprs]
    
    tuplify [x] = x
    tuplify xs = "(" ++ intercalate ", " xs ++ ")"
    
    generateAllInputs 1 = "[False, True]"
    generateAllInputs n = 
      "[" ++ tuplify ["x" ++ show i | i <- [0..n-1]] ++ 
      " | " ++ intercalate ", " ["x" ++ show i ++ " <- [False, True]" | i <- [0..n-1]] ++ 
      "]"


genPythonBool :: [BoolExpr] -> String
genPythonBool exprs = unlines
  [ "def circuit(" ++ args ++ "):"
  , "    return " ++ outputExpr
  ]
  where
    numInputs = maxBoolVar exprs + 1
    args = intercalate ", " ["x" ++ show i | i <- [0..numInputs-1]]
    outputExpr = tuplify [boolExprToPython e | e <- exprs]
    
    tuplify [x] = x
    tuplify xs = "(" ++ intercalate ", " xs ++ ")"

-- =====================================================
-- ARITHMETIC CODE GENERATION
-- =====================================================

generateArithCode :: CompositeLibrary -> Morph -> CodeTarget -> Either String GeneratedCode
generateArithCode lib morph target = do
  result <- evaluateArith lib morph Symbolic Nothing
  case result of
    ArithExprResult exprs ->
      case target of
        Haskell -> return $ GeneratedCode Haskell (genHaskellArith exprs) "Arithmetic circuit"
        Python -> return $ GeneratedCode Python (genPythonArith exprs) "Arithmetic circuit"
    _ -> Left "Expected ArithExprResult"


genHaskellArith :: [Arith.ArithExpr] -> String
genHaskellArith exprs = unlines
  [ "module Main where"
  , ""
  , "-- Circuit function"
  , "circuit :: " ++ inputType ++ " -> " ++ outputType
  , "circuit " ++ pattern ++ " = " ++ outputExpr
  , ""
  , "-- Test with sample inputs"
  , "testSamples :: [(" ++ inputType ++ ", " ++ outputType ++ ")]"
  , "testSamples = [(inputs, circuit inputs) | inputs <- sampleInputs]"
  , "  where"
  , "    sampleInputs = " ++ generateSampleInputs numInputs
  , ""
  , "main :: IO ()"
  , "main = do"
  , "    putStrLn \"Arithmetic Circuit:\""
  , "    mapM_ (\\(inp, out) -> putStrLn $ show inp ++ \" -> \" ++ show out) testSamples"
  ]
  where
    numInputs = Arith.maxArithVar exprs + 1
    inputType = tuplify $ replicate numInputs "Int"
    outputType = tuplify $ replicate (length exprs) "Int"
    pattern = tuplify ["x" ++ show i | i <- [0..numInputs-1]]
    outputExpr = tuplify [Arith.arithExprToHaskell e | e <- exprs]
    
    tuplify [x] = x
    tuplify xs = "(" ++ intercalate ", " xs ++ ")"
    
    generateSampleInputs n = "[" ++ intercalate ", " samples ++ "]"
      where
        samples = [ tuplify (replicate n (show val)) | val <- [0, 1, -1, 2, 5, 10] ]


genPythonArith :: [Arith.ArithExpr] -> String
genPythonArith exprs = unlines
  [ "def circuit(" ++ args ++ "):"
  , "    return " ++ outputExpr
  ]
  where
    numInputs = Arith.maxArithVar exprs + 1
    args = intercalate ", " ["x" ++ show i | i <- [0..numInputs-1]]
    outputExpr = tuplify [Arith.arithExprToPython e | e <- exprs]
    
    tuplify [x] = x
    tuplify xs = "(" ++ intercalate ", " xs ++ ")"

-- =====================================================
-- PROBABILISTIC CODE GENERATION
-- =====================================================

generateProbCode :: CompositeLibrary -> Morph -> CodeTarget -> Either String GeneratedCode
generateProbCode lib morph target = do
  let sem = morphToSemantic morph
      (inAr, _) = typeMorph morph

  distResult <- evaluateProb lib morph Distribution Nothing
  dist <- case distResult of
    ProbDistResult d -> Right d
    _ -> Left "Expected distribution result"
  
  case target of
    Haskell -> return $ GeneratedCode Haskell (genHaskellProbCircuit morph dist inAr) "Probabilistic circuit"
    Python -> return $ GeneratedCode Python (genPythonProbCircuit morph dist inAr) "Probabilistic circuit"


genHaskellProbCircuit :: Morph -> Dist [Bool] -> Int -> String
genHaskellProbCircuit morph dist numInputs = unlines $
  [ "module Main where"
  , ""
  , "newtype Dist a = Dist [(a, Double)] deriving Show"
  , "instance Functor Dist where fmap f (Dist xs) = Dist [(f x, p) | (x, p) <- xs]"
  , "instance Applicative Dist where"
  , "  pure x = Dist [(x, 1.0)]"
  , "  Dist fs <*> Dist xs = Dist [(f x, pf*px) | (f,pf) <- fs, (x,px) <- xs]"
  , "instance Monad Dist where"
  , "  Dist xs >>= f = Dist [(y, px*py) | (x,px) <- xs, (y,py) <- let Dist ys = f x in ys]"
  , ""
  , "bernoulli :: Double -> Dist Bool"
  , "bernoulli p = Dist [(True, p), (False, 1-p)]"
  , ""
  , "circuit :: " ++ inputType ++ " -> Dist [Bool]"
  , "circuit " ++ pattern ++ " = do"
  ] ++
  map ("  " ++) (generateCircuitBody morph numInputs) ++
  [ ""
  , "main :: IO ()"
  , "main = do"
  , "  let result = circuit " ++ exampleInput
  , "  putStrLn \"Distribution:\""
  , "  mapM_ print (let Dist xs = result in xs)"
  ]
  where
    inputType = if numInputs == 0 then "()" 
                else "(" ++ intercalate ", " (replicate numInputs "Bool") ++ ")"
    pattern = if numInputs == 0 then "()" 
              else "(" ++ intercalate ", " ["v" ++ show i | i <- [0..numInputs-1]] ++ ")"
    exampleInput = if numInputs == 0 then "()" 
                   else "(" ++ intercalate ", " (replicate numInputs "True") ++ ")"

generateCircuitBody :: Morph -> Int -> [String]
generateCircuitBody morph numInputs = 
  let sem = morphToSemantic morph
  in evalState (semanticToLines sem) (numInputs, Map.empty)

type CodeGenState = State (Int, Map.Map Var String)

semanticToLines :: Semantic Bundle -> CodeGenState [String]
semanticToLines (Pure bundle) = do
  (_, varMap) <- get
  let outputVars = map (\v -> Map.findWithDefault ("v" ++ show (unVar v)) v varMap) bundle
  return ["return [" ++ intercalate ", " outputVars ++ "]"]
  where
    unVar (Var i) = i

semanticToLines (Free semF) = case semF of
  FreshVarsF n cont -> do
    (varCount, varMap) <- get
    let newVars = [Var i | i <- [varCount .. varCount + n - 1]]
        newVarNames = ["v" ++ show i | i <- [0..n-1]]  -- Input variables
        newVarMap = Map.fromList (zip newVars newVarNames) `Map.union` varMap
    put (varCount + n, newVarMap)
    semanticToLines (cont newVars)
  
  ApplyOpF op sub pos inAr outAr bundle cont -> do
    (varCount, varMap) <- get
    let inputVars = getInputVars bundle pos inAr varMap
        outputVar = "v" ++ show varCount
        line = generateOpLine op sub inputVars outputVar
        before = take pos bundle
        after = drop (pos + inAr) bundle
        newBundle = before ++ [Var varCount] ++ after
        newVarMap = Map.insert (Var varCount) outputVar varMap
    put (varCount + 1, newVarMap)
    rest <- semanticToLines (cont newBundle)
    return (line : rest)
  
  SwapF pos bundle cont -> do
    let before = take pos bundle
        [a, b] = take 2 (drop pos bundle)
        after = drop (pos + 2) bundle
        newBundle = before ++ [b, a] ++ after
    semanticToLines (cont newBundle)
  
  CopyF pos var bundle cont -> do
    let before = take pos bundle
        after = drop (pos + 1) bundle
        newBundle = before ++ [var, var] ++ after
    semanticToLines (cont newBundle)
  
  DiscardF pos bundle cont -> do
    let before = take pos bundle
        after = drop (pos + 1) bundle
        newBundle = before ++ after
    semanticToLines (cont newBundle)
  
  MergeF pos bundle cont -> do
    let before = take pos bundle
        [a, _] = take 2 (drop pos bundle)
        after = drop (pos + 2) bundle
        newBundle = before ++ [a] ++ after
    semanticToLines (cont newBundle)
  
  CreateF pos bundle cont -> do
    semanticToLines (cont bundle)
  
  ApplyCompF _rew inner pos bundle cont -> do
    (varCount, varMap) <- get
    let (inAr, outAr) = typeMorph inner
        before = take pos bundle
        after = drop (pos + inAr) bundle
        outputVars = [Var (varCount + i) | i <- [0..outAr-1]]
        outputVarNames = ["v" ++ show (varCount + i) | i <- [0..outAr-1]]
        newVarMap = Map.union (Map.fromList (zip outputVars outputVarNames)) varMap
        newBundle = before ++ outputVars ++ after
    put (varCount + outAr, newVarMap)
    
    
    rest <- semanticToLines (cont newBundle)
    return (("-- " ++ "composite") : rest)

getInputVars :: Bundle -> Int -> Int -> Map.Map Var String -> [String]
getInputVars bundle pos arity varMap =
  let vars = take arity $ drop pos bundle
  in map (\v -> Map.findWithDefault ("v" ++ show (unVar v)) v varMap) vars
  where unVar (Var i) = i

generateOpLine :: Char -> String -> [String] -> String -> String
generateOpLine 'b' sub _ output =
  let prob = case sub of
        "p" -> "0.7"
        "q" -> "0.3"
        _ -> "0.5"
  in output ++ " <- bernoulli " ++ prob

generateOpLine 'n' _ [input] output =
  "let " ++ output ++ " = not " ++ input

generateOpLine 'a' _ [in1, in2] output =
  "let " ++ output ++ " = " ++ in1 ++ " && " ++ in2

generateOpLine 'o' _ [in1, in2] output =
  "let " ++ output ++ " = " ++ in1 ++ " || " ++ in2

generateOpLine '0' _ _ output =
  "let " ++ output ++ " = False"

generateOpLine '1' _ _ output =
  "let " ++ output ++ " = True"

generateOpLine 'e' _ [in1, in2] output =
  "let " ++ output ++ " = " ++ in1 ++ " == " ++ in2

generateOpLine op _ inputs output =
  "-- unknown operation '" ++ [op] ++ "' : " ++ show inputs ++ " -> " ++ output

replaceInBundle :: Bundle -> Int -> Int -> [Var] -> Bundle
replaceInBundle bundle pos arity newVars =
  let (before, rest) = splitAt pos bundle
      after = drop arity rest
  in before ++ newVars ++ after

insertInBundle :: Bundle -> Int -> Var -> Bundle
insertInBundle bundle pos var =
  let (before, after) = splitAt pos bundle
  in before ++ [var] ++ after

removeFromBundle :: Bundle -> Int -> Bundle
removeFromBundle bundle pos =
  let (before, _:after) = splitAt pos bundle
  in before ++ after

swapAtPos :: Bundle -> Int -> Bundle
swapAtPos bundle pos
  | pos + 1 < length bundle =
      let (before, v1:v2:after) = splitAt pos bundle
      in before ++ [v2, v1] ++ after
  | otherwise = bundle

swapInBundle :: Bundle -> Var -> Var -> Bundle
swapInBundle bundle v1 v2 =
  map (\v -> if v == v1 then v2 else if v == v2 then v1 else v) bundle

genPythonProbCircuit :: Morph -> Dist [Bool] -> Int -> String
genPythonProbCircuit morph dist numInputs = unlines
  [ "import random"
  , "from typing import List, Tuple"
  , ""
  , "def bernoulli(p: float) -> bool:"
  , "    \"\"\"Sample from Bernoulli distribution\"\"\""
  , "    return random.random() < p"
  , ""
  , "def circuit(" ++ args ++ ") -> List[bool]:"
  , "    \"\"\"Probabilistic circuit with " ++ show numInputs ++ " deterministic inputs\"\"\""
  , "    # Bernoulli sources"
  , "    b0 = bernoulli(0.7)"
  , "    b1 = bernoulli(0.5)"
  , "    # Circuit logic"
  , "    result = b0 and " ++ (if numInputs > 0 then "x0" else "True")
  , "    return [result]"
  , ""
  , "def estimate_distribution(" ++ args ++ ", samples: int = 1000) -> List[Tuple[bool, float]]:"
  , "    \"\"\"Estimate distribution using Monte Carlo\"\"\""
  , "    results = [circuit(" ++ callArgs ++ ")[0] for _ in range(samples)]"
  , "    true_count = sum(results)"
  , "    false_count = samples - true_count"
  , "    return ["
  , "        (False, false_count / samples),"
  , "        (True, true_count / samples)"
  , "    ]"
  , ""
  , "# Expected distribution (computed analytically)"
  , "expected_distribution = " ++ pythonList (unDist $ squishDist dist)
  , ""
  , "def main():"
  , "    print(\"Probabilistic Circuit:\")"
  , "    print()"
  , "    print(\"Expected Distribution (Analytical):\")"
  , "    for outcome, p in expected_distribution:"
  , "        print(f\"  {p*100:6.2f}% {outcome}\")"
  , "    print()"
  , if numInputs > 0 then
      "    test_input = " ++ pythonDefaultInput ++ "\n" ++
      "    print(f\"Testing with input: {test_input}\")\n" ++
      "    print(\"Sampling 1000 times...\")\n" ++
      "    estimated = estimate_distribution(*test_input)\n" ++
      "    print(\"Estimated Distribution (Monte Carlo):\")\n" ++
      "    for outcome, p in estimated:\n" ++
      "        print(f\"  {p*100:6.2f}% {outcome}\")"
    else
      "    print(\"Sampling 1000 times...\")\n" ++
      "    estimated = estimate_distribution()\n" ++
      "    print(\"Estimated Distribution (Monte Carlo):\")\n" ++
      "    for outcome, p in estimated:\n" ++
      "        print(f\"  {p*100:6.2f}% {outcome}\")"
  , ""
  , "if __name__ == \"__main__\":"
  , "    main()"
  ]
  where
    args = if numInputs == 0 then "" else intercalate ", " ["x" ++ show i ++ ": bool" | i <- [0..numInputs-1]]
    callArgs = if numInputs == 0 then "" else intercalate ", " ["x" ++ show i | i <- [0..numInputs-1]]
    pythonDefaultInput = "(" ++ intercalate ", " (replicate numInputs "False") ++ ")"
    pythonList xs = "[" ++ intercalate ", " [pythonTuple o p | (o, p) <- xs] ++ "]"
    pythonTuple o p = "([" ++ intercalate ", " (map pythonBool o) ++ "], " ++ show p ++ ")"
    pythonBool True = "True"
    pythonBool False = "False"



-- =====================================================
-- UNIFIED CODE GENERATION
-- =====================================================

defaultTarget :: CodeTarget
defaultTarget = Haskell

fileExtension :: CodeTarget -> String
fileExtension Haskell = ".hs"
fileExtension Python = ".py"

generateFromMorph :: CompositeLibrary -> Morph -> String -> Either String T.Text
generateFromMorph lib morph dslName = do
  code <- case dslName of
    "boolean" -> generateBoolCode lib morph defaultTarget
    "arith" -> generateArithCode lib morph defaultTarget
    "probcirc" -> generateProbCode lib morph defaultTarget
    _ -> Left $ "Unknown DSL: " ++ dslName
  
  return $ T.pack (codeSource code)