{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
module SemanticFree
  ( Semantic(..)
  , SemanticF(..)
  , Var(..)
  , Bundle
  , Wire
  , CompositeLibrary
  , CompositeOp(..)
  , standardComposites
  , defineComposite
  , lookupComposite
  , freshVars
  , applyOp
  , applySwap
  , applyCopy
  , applyDiscard
  , applyComp
  , applyMerge
  , applyCreate
  , morphToSemantic
  , prettySemantic
  , foldSemantic
  , defineCompositeOp
  , extractFinalBundle
  , prettySemanticClean
  ) where



import Morph hiding (compMorph)
import Control.Monad (ap)
import qualified Data.Map as Map
import Data.List (intercalate)  
newtype Var = Var Int
  deriving (Eq, Ord)

type Bundle = [Wire]
type Wire = Var

instance Show Var where
  show (Var i) = "v" ++ show i

-- =====================================
-- FREE MONAD WITH STRUCTURAL OPS
-- =====================================

data SemanticF next
    = FreshVarsF Int (Bundle -> next)
    
    -- Structural operations
    | SwapF Int Bundle (Bundle -> next)
    | CopyF Int Var Bundle (Bundle -> next)
    | DiscardF Int Bundle (Bundle -> next)
    | MergeF Int Bundle (Bundle -> next)
    | CreateF Int Bundle (Bundle -> next)
    -- Generative operations
    | ApplyOpF
        { opChar   :: Char
        , opStyle  :: String
        , opPos    :: Int
        , opInAr   :: Int
        , opOutAr  :: Int
        , opBundle :: Bundle
        , opCont   :: Bundle -> next
        }
    | ApplyCompF Rew Morph Int Bundle (Bundle -> next)
    deriving Functor

data Semantic a
    = Pure a
    | Free (SemanticF (Semantic a))

instance Functor Semantic where
    fmap f (Pure x) = Pure (f x)
    fmap f (Free x) = Free (fmap (fmap f) x)

instance Applicative Semantic where
    pure = Pure
    (<*>) = ap

instance Monad Semantic where
    return = pure
    Pure x >>= f = f x
    Free x >>= f = Free (fmap (>>= f) x)

-- =====================================
-- SMART CONSTRUCTORS
-- =====================================

freshVars :: Int -> Semantic Bundle
freshVars n = Free (FreshVarsF n Pure)

-- Structural operations
applySwap :: Int -> Bundle -> Semantic Bundle
applySwap pos bundle = Free (SwapF pos bundle Pure)

applyCopy :: Int -> Var -> Bundle -> Semantic Bundle
applyCopy pos var bundle = Free (CopyF pos var bundle Pure)

applyDiscard :: Int -> Bundle -> Semantic Bundle
applyDiscard pos bundle = Free (DiscardF pos bundle Pure)

applyMerge :: Int -> Bundle -> Semantic Bundle
applyMerge pos bundle = Free (MergeF pos bundle Pure)

applyCreate :: Int -> Bundle -> Semantic Bundle
applyCreate pos bundle = Free (CreateF pos bundle Pure)

-- Generative operation
applyOp :: Char -> Style -> Int -> Int -> Int -> Bundle -> Semantic Bundle
applyOp c style pos inAr outAr bundle =
    Free (ApplyOpF c "" pos inAr outAr bundle Pure)

applyComp :: Rew -> Morph -> Int -> Bundle -> Semantic Bundle
applyComp rew morph pos bundle =
    Free (ApplyCompF rew morph pos bundle Pure)

-- =====================================
-- MORPH → SEMANTIC
-- =====================================
morphToSemanticWithLib :: CompositeLibrary -> Morph -> Semantic Bundle
morphToSemanticWithLib lib (Start n) = freshVars n

morphToSemanticWithLib lib (Op m i (Base (Sig c style a b))) = do
    bundle <- morphToSemanticWithLib lib m
    
    -- Check if this is a named composite operation
    case lookupComposite (c:"") lib of
        Just comp -> expandComposite comp i bundle
        Nothing -> 
            -- Check if it's a structural operation
            case (c, style, a, b) of
                ('x', (Nothing , "1") , 2, 2) -> applySwap i bundle
                ('c', (Nothing , "2"), 1, 2) -> 
                    let var = bundle !! i
                    in applyCopy i var bundle
                ('d', (Nothing , "2"), 1, 0) -> applyDiscard i bundle
                _ -> applyOp c style i a b bundle

morphToSemanticWithLib lib (Op m i (Comp rew inner)) = do
    bundle <- morphToSemanticWithLib lib m
    applyComp rew inner i bundle

morphToSemantic :: Morph -> Semantic Bundle
morphToSemantic = morphToSemanticWithLib standardComposites

-- =====================================================
-- COMPOSITE OPERATION LIBRARY
-- =====================================================

data CompositeOp = CompositeOp
    { compName    :: String
    , compInArity :: Int
    , compOutArity :: Int
    , composMorph   :: Morph
    , compDSL      :: String
    } deriving (Show)

type CompositeLibrary = Map.Map String CompositeOp
standardComposites :: CompositeLibrary
standardComposites = Map.empty

defineCompositeOp :: Char -> String -> Morph -> String -> CompositeLibrary -> CompositeLibrary
defineCompositeOp opChar opStyle morph dslName lib =
    let (inAr, outAr) = typeMorph morph
        name = [opChar] ++ opStyle
        comp = CompositeOp name inAr outAr morph dslName
    in Map.insert name comp lib

buildStandardLibrary :: CompositeLibrary
buildStandardLibrary = Map.empty


defineComposite :: String -> Morph -> String -> CompositeLibrary -> CompositeLibrary
defineComposite name morph dslName lib =
    let (inAr, outAr) = typeMorph morph
        comp = CompositeOp name inAr outAr morph dslName
    in Map.insert name comp lib

lookupComposite :: String -> CompositeLibrary -> Maybe CompositeOp
lookupComposite = Map.lookup

expandComposite :: CompositeOp -> Int -> Bundle -> Semantic Bundle
expandComposite comp pos bundle = do
    applyComp (RI (composMorph comp)) (composMorph comp) pos bundle

-- =====================================================
-- HASKELL CODE GENERATION
-- =====================================================
extractFinalBundle :: Semantic Bundle -> Bundle
extractFinalBundle (Pure b) = b
extractFinalBundle (Free (FreshVarsF n k)) =
    let vars = [Var i | i <- [0..n-1]]
    in extractFinalBundle (k vars)
extractFinalBundle (Free (SwapF pos bundle k)) =
    let before = take pos bundle
        [a, b] = take 2 (drop pos bundle)
        after = drop (pos + 2) bundle
        newBundle = before ++ [b, a] ++ after
    in extractFinalBundle (k newBundle)
extractFinalBundle (Free (CopyF pos var bundle k)) =
    let before = take pos bundle
        after = drop (pos + 1) bundle
        newBundle = before ++ [var, var] ++ after
    in extractFinalBundle (k newBundle)
extractFinalBundle (Free (DiscardF pos bundle k)) =
    let before = take pos bundle
        after = drop (pos + 1) bundle
        newBundle = before ++ after
    in extractFinalBundle (k newBundle)
extractFinalBundle (Free (MergeF pos bundle k)) =
    let before = take pos bundle
        [a, _] = take 2 (drop pos bundle)
        after = drop (pos + 2) bundle
        newBundle = before ++ [a] ++ after
    in extractFinalBundle (k newBundle)
extractFinalBundle (Free (CreateF pos bundle k)) =
    let before = take pos bundle
        after = drop pos bundle
        newVar = Var 0
        newBundle = before ++ [newVar] ++ after
    in extractFinalBundle (k newBundle)
extractFinalBundle (Free (ApplyOpF c s pos inA outA bundle k)) =
    let before = take pos bundle
        outputs = [Var 0]
        after = drop (pos + inA) bundle
        newBundle = before ++ outputs ++ after
    in extractFinalBundle (k newBundle)
extractFinalBundle (Free (ApplyCompF _ inner pos bundle k)) =
    let (_, outA) = typeMorph inner
        before = take pos bundle
        outputs = [Var 0]
        after = drop (pos + outA) bundle
        newBundle = before ++ outputs ++ after
    in extractFinalBundle (k newBundle)
    
-- =====================================
-- PRETTY PRINT
-- =====================================

prettySemantic :: Semantic Bundle -> [String]
prettySemantic sem = 
    let (inArity, _) = inferArity sem
        header = "function(" ++ intercalate ", " ["v" ++ show i | i <- [0..inArity-1]] ++ "):"
    in header : map ("  " ++) (go 0 inArity sem)
  where
    inferArity :: Semantic Bundle -> (Int, Int)
    inferArity (Free (FreshVarsF n _)) = (n, 0)  -- (inputs, outputs)
    inferArity _ = (0, 0)
    
    go :: Int -> Int -> Semantic Bundle -> [String]
    go freshCounter inputCount (Pure bundle) = 
        ["return " ++ show bundle]
    
    go freshCounter inputCount (Free (FreshVarsF n cont)) =
        let vars = [Var i | i <- [freshCounter .. freshCounter + n - 1]]
            rest = go (freshCounter + n) inputCount (cont vars)
        in if freshCounter == 0
           then rest
           else ("let " ++ show vars ++ " = fresh(" ++ show n ++ ")") : rest
    
    go freshCounter inputCount (Free (SwapF pos bundle cont)) =
        let before = take pos bundle
            [a, b] = take 2 (drop pos bundle)
            after = drop (pos + 2) bundle
            newBundle = before ++ [b, a] ++ after
            line = "let " ++ show newBundle ++ " = swap(" ++ show [a, b] ++ ")"
        in line : go freshCounter inputCount (cont newBundle)
    
    go freshCounter inputCount (Free (CopyF pos var bundle cont)) =
        let before = take pos bundle
            after = drop (pos + 1) bundle
            newBundle = before ++ [var, var] ++ after
            line = "let " ++ show newBundle ++ " = copy(" ++ show var ++ ")"
        in line : go freshCounter inputCount (cont newBundle)
    
    go freshCounter inputCount (Free (DiscardF pos bundle cont)) =
        let before = take pos bundle
            var = bundle !! pos
            after = drop (pos + 1) bundle
            newBundle = before ++ after
            line = "let " ++ show newBundle ++ " = discard(" ++ show var ++ ")"
        in line : go freshCounter inputCount (cont newBundle)
    
    go freshCounter inputCount (Free (MergeF pos bundle cont)) =
        let before = take pos bundle
            [a, b] = take 2 (drop pos bundle)
            after = drop (pos + 2) bundle
            newBundle = before ++ [a] ++ after
            line = "let " ++ show newBundle ++ " = merge(" ++ show [a, b] ++ ")"
        in line : go freshCounter inputCount (cont newBundle)
        
    go freshCounter inputCount (Free (CreateF pos bundle cont)) =
        let before = take pos bundle
            after = drop pos bundle
            newVar = Var freshCounter
            newBundle = before ++ [newVar] ++ after
            line = "let " ++ show newBundle ++ " = create()"
        in line : go (freshCounter + 1) inputCount (cont newBundle)

    go freshCounter inputCount (Free (ApplyOpF c s pos inA outA bundle cont)) =
        let before = take pos bundle
            inputs = take inA (drop pos bundle)
            after = drop (pos + inA) bundle
            outputs = [Var i | i <- [freshCounter .. freshCounter + outA - 1]]
            newBundle = before ++ outputs ++ after
            opName = [c] ++ s
            line = "let " ++ show outputs ++ " = " ++ opName ++ "(" ++ show inputs ++ ")"
        in line : go (freshCounter + outA) inputCount (cont newBundle)
    
    go freshCounter inputCount (Free (ApplyCompF _rew inner pos bundle cont)) =
        let (inA, outA) = typeMorph inner
            before = take pos bundle
            inputs = take inA (drop pos bundle)
            after = drop (pos + inA) bundle
            outputs = [Var i | i <- [freshCounter .. freshCounter + outA - 1]]
            
            -- Expand the inner composition with indentation
            innerSem = morphToSemantic inner
            innerHeader = "function(" ++ intercalate ", " (map show inputs) ++ "):"
            innerBody = go 0 inA innerSem
            indentedInner = map ("  " ++) (innerHeader : map ("  " ++) innerBody)
            
            headerLine = "let " ++ show outputs ++ " = composite:"
            
            -- Continue with outer morphism
            newBundle = before ++ outputs ++ after
            restLines = go (freshCounter + outA) inputCount (cont newBundle)
        in (headerLine : indentedInner) ++ restLines


-- CLEANED VERSION FOR PRETTY PRINT
prettySemanticClean :: Semantic Bundle -> [String]
prettySemanticClean sem = 
    let (inArity, _) = inferArity sem
        header = "function(" ++ intercalate ", " ["v" ++ show i | i <- [0..inArity-1]] ++ "):"
    in header : map ("  " ++) (goClean 0 inArity sem)
  where
    inferArity :: Semantic Bundle -> (Int, Int)
    inferArity (Free (FreshVarsF n _)) = (n, 0)
    inferArity _ = (0, 0)
    
    goClean :: Int -> Int -> Semantic Bundle -> [String]
    goClean freshCounter inputCount (Pure bundle) = 
        ["return " ++ show bundle]
    
    goClean freshCounter inputCount (Free (FreshVarsF n cont)) =
        let vars = [Var i | i <- [freshCounter .. freshCounter + n - 1]]
        in if freshCounter == 0
           then goClean (freshCounter + n) inputCount (cont vars)
           else goClean (freshCounter + n) inputCount (cont vars)
    
    -- HIDE structural operations - just pass through
    goClean freshCounter inputCount (Free (SwapF pos bundle cont)) =
        let before = take pos bundle
            [a, b] = take 2 (drop pos bundle)
            after = drop (pos + 2) bundle
            newBundle = before ++ [b, a] ++ after
        in goClean freshCounter inputCount (cont newBundle)
    
    goClean freshCounter inputCount (Free (CopyF pos var bundle cont)) =
        let before = take pos bundle
            after = drop (pos + 1) bundle
            newBundle = before ++ [var, var] ++ after
        in goClean freshCounter inputCount (cont newBundle)
    
    goClean freshCounter inputCount (Free (DiscardF pos bundle cont)) =
        let before = take pos bundle
            after = drop (pos + 1) bundle
            newBundle = before ++ after
        in goClean freshCounter inputCount (cont newBundle)
    
    goClean freshCounter inputCount (Free (MergeF pos bundle cont)) =
        let before = take pos bundle
            [a, _] = take 2 (drop pos bundle)
            after = drop (pos + 2) bundle
            newBundle = before ++ [a] ++ after
        in goClean freshCounter inputCount (cont newBundle)
        
    goClean freshCounter inputCount (Free (CreateF pos bundle cont)) =
        let before = take pos bundle
            after = drop pos bundle
            newVar = Var freshCounter
            newBundle = before ++ [newVar] ++ after
        in goClean (freshCounter + 1) inputCount (cont newBundle)

    -- SHOW actual operations
    goClean freshCounter inputCount (Free (ApplyOpF c s pos inA outA bundle cont)) =
        let before = take pos bundle
            inputs = take inA (drop pos bundle)
            after = drop (pos + inA) bundle
            outputs = [Var i | i <- [freshCounter .. freshCounter + outA - 1]]
            newBundle = before ++ outputs ++ after
            opName = [c] ++ s
            line = "let " ++ show outputs ++ " = " ++ opName ++ "(" ++ show inputs ++ ")"
        in line : goClean (freshCounter + outA) inputCount (cont newBundle)
    
    goClean freshCounter inputCount (Free (ApplyCompF _rew inner pos bundle cont)) =
        let (inA, outA) = typeMorph inner
            before = take pos bundle
            inputs = take inA (drop pos bundle)
            after = drop (pos + inA) bundle
            outputs = [Var i | i <- [freshCounter .. freshCounter + outA - 1]]
            newBundle = before ++ outputs ++ after
            innerSem = morphToSemantic inner
            innerLines = goClean 0 inA innerSem            
            restLines = goClean (freshCounter + outA) inputCount (cont newBundle)
        in innerLines ++ restLines
-- =====================================
-- FOLD
-- =====================================

foldSemantic
  :: (a -> r)
  -> (Int -> (Bundle -> r) -> r)                                          -- FreshVars
  -> (Int -> Bundle -> (Bundle -> r) -> r)                                -- Swap
  -> (Int -> Var -> Bundle -> (Bundle -> r) -> r)                         -- Copy
  -> (Int -> Bundle -> (Bundle -> r) -> r)                                -- Discard
  -> (Int -> Bundle -> (Bundle -> r) -> r)                                -- Merge NEW
  -> (Int -> Bundle -> (Bundle -> r) -> r)                                -- Create NEW
  -> (Char -> String -> Int -> Int -> Int -> Bundle -> (Bundle -> r) -> r) -- ApplyOp
  -> (Rew -> Morph -> Int -> Bundle -> (Bundle -> r) -> r)               -- ApplyComp
  -> Semantic a
  -> r
foldSemantic pureK freshK swapK copyK discardK mergeK createK opK compK = go
  where
    go (Pure x) = pureK x
    go (Free (FreshVarsF n k)) = freshK n (go . k)
    go (Free (SwapF p b k)) = swapK p b (go . k)
    go (Free (CopyF p v b k)) = copyK p v b (go . k)
    go (Free (DiscardF p b k)) = discardK p b (go . k)
    go (Free (MergeF p b k)) = mergeK p b (go . k)         
    go (Free (CreateF p b k)) = createK p b (go . k)       
    go (Free (ApplyOpF c s p i o b k)) = opK c s p i o b (go . k)
    go (Free (ApplyCompF r m p b k)) = compK r m p b (go . k)
