{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}

module DSL.ProbabilisticMonad
  ( Prob
  , Dist(..)
  , ProbDSL(..)
  , runProbDSL
  , squishDist
  , uniform
  , bernoulli
  , conditionOn
  , liftDist
  , strengthL
  , strengthR
  ) where

import Control.Monad.Except
import qualified Data.Map as M
import Data.List (intercalate)

-- =====================================================
-- PROBABILITY DISTRIBUTION
-- =====================================================

type Prob = Double

newtype Dist a = Dist { unDist :: [(a, Prob)] }
  deriving (Eq, Functor)

instance (Show a, Ord a) => Show (Dist a) where
  show d = formatDist (squishDist d)
    where
      formatDist (Dist outcomes) = 
        unlines [padded x ++ " | " ++ show p | (x, p) <- outcomes]
        where
          maxLen = maximum $ map (length . show . fst) outcomes
          padded x = replicate (maxLen - length (show x)) ' ' ++ show x

squishDist :: Ord a => Dist a -> Dist a
squishDist (Dist xs) = Dist $ M.toList $ M.fromListWith (+) xs

normalize :: [(a, Prob)] -> [(a, Prob)]
normalize xs = [(x, p / total) | (x, p) <- xs]
  where total = sum (map snd xs)

evalProb :: (a -> Bool) -> Dist a -> Prob
evalProb pred (Dist xs) = sum [p | (x, p) <- xs, pred x]

conditionOn :: Ord a => (a -> Bool) -> Dist a -> Dist a
conditionOn pred (Dist xs) = Dist . normalize $ filter (pred . fst) xs

-- =====================================================
-- DISTRIBUTION HELPERS
-- =====================================================

uniform :: [a] -> Dist a
uniform [] = error "uniform: empty list"
uniform xs = Dist $ normalize [(x, 1.0) | x <- xs]

bernoulli :: Prob -> Dist Bool
bernoulli p
  | p < 0 || p > 1 = error "bernoulli: probability must be in [0,1]"
  | otherwise = Dist [(True, p), (False, 1 - p)]

-- =====================================================
-- FUNCTOR, APPLICATIVE, MONAD INSTANCES
-- =====================================================

instance Applicative Dist where
  pure x = Dist [(x, 1.0)]
  
  (Dist fs) <*> (Dist xs) = Dist
    [ (f x, pf * px)
    | (f, pf) <- fs
    , (x, px) <- xs
    ]

instance Monad Dist where
  (Dist xs) >>= f = Dist
    [ (y, px * py)
    | (x, px) <- xs
    , (y, py) <- unDist (f x)
    ]

-- =====================================================
-- PROBABILISTIC DSL MONAD
-- =====================================================

newtype ProbDSL a = ProbDSL 
  { unProbDSL :: ExceptT String Dist a }
  deriving (Functor, Applicative, Monad, MonadError String)

runProbDSL :: ProbDSL a -> Dist (Either String a)
runProbDSL (ProbDSL m) = runExceptT m

liftDist :: Dist a -> ProbDSL a
liftDist = ProbDSL . ExceptT . fmap Right

strengthL :: a -> ProbDSL b -> ProbDSL (a, b)
strengthL a mb = fmap (a,) mb

strengthR :: ProbDSL a -> b -> ProbDSL (a, b)
strengthR ma b = fmap (,b) ma