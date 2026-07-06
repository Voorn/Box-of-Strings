{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
module DSL.StandardMonad
  ( StandardDSL(..)
  , runStandardDSL
  , strengthL
  , strengthR
  ) where

import Control.Monad.Except

-- =====================================================
-- STANDARD DSL MONAD
-- =====================================================

newtype StandardDSL a = StandardDSL 
  { unStandardDSL :: Either String a }
  deriving (Functor, Applicative, Monad, MonadError String)

runStandardDSL :: StandardDSL a -> Either String a
runStandardDSL = unStandardDSL

strengthL :: a -> StandardDSL b -> StandardDSL (a, b)
strengthL a mb = fmap (a,) mb

strengthR :: StandardDSL a -> b -> StandardDSL (a, b)
strengthR ma b = fmap (,b) ma