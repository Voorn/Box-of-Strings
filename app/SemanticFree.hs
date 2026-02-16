{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
module SemanticFree
  ( Semantic(..)
  , SemanticF(..)
  , Var(..)
  , Bundle
  , Wire
  , freshVars
  , applyOp
  , applyComp
  , morphToSemantic
  , prettySemantic
  , foldSemantic
  ) where

import Morph
import Control.Monad (ap)

newtype Var = Var Int
  deriving (Eq, Ord)


type Bundle = [Wire]

instance Show Var where
  show (Var i) = "v" ++ show i


type Wire = Var

-- =====================================
-- FREE MONAD SEMANTIC REPRESENTATION
-- =====================================


data SemanticF next
    = FreshVarsF Int (Bundle -> next)
    | ApplyOpF
        { opChar   :: Char
        , opStyle  :: String
        , opPos    :: Int
        , opInAr   :: Int
        , opOutAr  :: Int
        , opInput  :: Bundle
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

applyOp :: Char -> String -> Int -> Int -> Int -> Bundle -> Semantic Bundle
applyOp c style pos inAr outAr vars =
    Free (ApplyOpF c style pos inAr outAr vars Pure)

applyComp :: Rew -> Morph -> Int -> Bundle -> Semantic Bundle
applyComp rew morph pos vars =
    Free (ApplyCompF rew morph pos vars Pure)

-- =====================================
-- MORPH → SEMANTIC
-- =====================================

morphToSemantic :: Morph -> Semantic Bundle
morphToSemantic (Start n) = freshVars n
morphToSemantic (Op m i (Base (Sig c style a b))) = do
    vars <- morphToSemantic m
    applyOp c style i a b vars
morphToSemantic (Op m i (Comp rew inner)) = do
    vars <- morphToSemantic m
    applyComp rew inner i vars

-- =====================================
-- FOLD
-- =====================================

foldSemantic
  :: (a -> r)
  -> (Int -> (Bundle -> r) -> r)
  -> (Char -> String -> Int -> Int -> Int -> Bundle -> (Bundle -> r) -> r)
  -> (Rew -> Morph -> Int -> Bundle -> (Bundle -> r) -> r)
  -> Semantic a
  -> r
foldSemantic pureK freshK opK compK = go
  where
    go (Pure x) = pureK x
    go (Free (FreshVarsF n k)) = freshK n (go . k)
    go (Free (ApplyOpF c s p i o vs k)) = opK c s p i o vs (go . k)
    go (Free (ApplyCompF r m p vs k)) = compK r m p vs (go . k)

showRew :: Rew -> String
showRew (RI _) = "RI"
showRew (RS MEqual _) = "RE"
showRew (RS MLarger _) = "RL"
showRew (RS MSmaller _) = "RS"

splice :: Int -> Int -> Bundle -> Bundle -> Bundle
splice pos inAr oldVars newVars =
    let (l, rest) = splitAt pos oldVars
        (_, r)    = splitAt inAr rest
    in l ++ newVars ++ r

-- =====================================
-- PRETTY SEMANTIC
-- =====================================

prettySemantic :: Semantic a -> [String]
prettySemantic sem = go 0 sem
  where
    go :: Int -> Semantic a -> [String]
    go n (Pure _) = ["return vars"]

    go n (Free (FreshVarsF k cont)) =
        let vars = map (\i -> Var (n+i)) [0..k-1]
            line = "Fresh vars: " ++ show vars
        in line : go (n+k) (cont vars)

    go n (Free (ApplyOpF c s pos inA outA vars cont)) =
        let ins  = take inA (drop pos vars)
            outs = map (\i -> Var (n+i)) [0..outA-1]
            line = show ins ++ " ──[" ++ [c] ++ s ++ "]@" ++ show pos ++ "-> " ++ show outs
        in line : go (n + outA) (cont outs)

    go n (Free (ApplyCompF _rew _m pos vars cont)) =
        let line = "Composition at pos " ++ show pos ++ " with vars: " ++ show vars
        in line : go n (cont vars)
