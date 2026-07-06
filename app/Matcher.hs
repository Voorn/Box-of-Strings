{-# LANGUAGE InstanceSigs #-}
module Matcher where

import Data.List

inList :: Eq a => a -> [a] -> Bool
inList _ [] = False
inList c (d : s) = c == d || inList c s

data Compare =
    Sim
    |   Before
    |   After

-- Matcher: Check if latter can be made to match former. Return matching function.
-- Property for -mat :: Matcher a-
-- 1) if -mat x y = Just f- then -f x == Just y- 
type Matcher a = a -> a -> Maybe (a -> Maybe a)

-- Order matcher, orders elements such that possible matching elements are clustered.
-- Property for -mat :: Matcher a- and -mord :: MatchOrd a-
-- 1) If -mord x y == Before- and -mat y
type MatchOrd a = a -> a -> Compare



trivialmatch :: Eq a => Matcher a
trivialmatch x y
    |   x == y      =   Just Just
    |   otherwise   =   Nothing

--type ExpL = (String , Int)


newtype Exp = Pol (Poly Char) 
    deriving (Eq , Ord)

constExp :: Int -> Exp 
constExp 0 = Pol []
constExp i = Pol [(i , [])]

linExp :: Char -> Int -> Exp 
linExp c 0 = Pol [(1 , [c])]
linExp c i = Pol [(i , []) , (1 , [c])]

instance Show Exp where
    show :: Exp -> String
    show (Pol pol) = showPoly pol

smallLet :: Char -> Bool
smallLet c  = inList c "abcdefghijklmnopqrstuvwxyz"

bigLet :: Char -> Bool
bigLet c    = inList c "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

type Subst = [(Char , Exp)]

addSubst :: (Char , Exp) -> Subst -> Maybe Subst
addSubst x [] = Just [x]
addSubst (c , l) ((d , r) : rest)
    |   c < d       =   Just ((c , l) : (d , r) : rest)
    |   c > d       =   fmap ((d , r) :) (addSubst (c , l) rest)
    |   otherwise   =   Nothing

addSubsts :: Subst -> Subst -> Maybe Subst
addSubsts [] sub = Just sub
addSubsts (x : dub) sub = addSubsts dub sub >>= \rub -> addSubst x rub

matchExp :: Exp -> Exp -> Maybe Subst
matchExp (Pol [(1 , [c])]) (Pol pal) =   
    if bigLet c || pal == [(1 , [c])]
    then Just [(c , Pol pal)]
    else Nothing    
matchExp (Pol [(i , []) , (1 , [c])]) (Pol pal) =   
    minusPoly pal i >>= \pal' -> 
    if bigLet c || pal' == [(1 , [c])]
    then Just [(c , Pol pal')]
    else Nothing    
matchExp (Pol pol) (Pol pal)
    |   pol == pal      =   Just []
    |   otherwise       =   Nothing
--     |   i == j      =   Just []
--     |   otherwise   =   Nothing
-- matchExp (Lin c i) (Const j)
--     |   bigLet c && i <= j  =   Just [(c , Const (j-i))]
--     |   otherwise           =   Nothing
-- matchExp (Const _) (Lin _ _) = Nothing
-- matchExp (Lin c i) (Lin d j)
--     |   bigLet c && i <= j  =   Just [(c , Lin d (j-i))]
--     |   c == d && i == j    =   Just [(c , Lin c 0)]
--     |   otherwise           =   Nothing --Just [] 

-- substLin :: Int -> Exp -> Exp
-- substLin i (Const j) = Const (i + j)
-- substLin i (Lin c j) = Lin c (i+j)


substChar :: Char -> Subst -> Maybe (Poly Char)
substChar c []
    |   bigLet c    =   Nothing 
    |   otherwise   =   Just [(1 , [c])]
substChar c ((d , Pol pol) : rest)
    |   c < d && bigLet c   =   Nothing 
    |   c < d               =   Just [(1 , [c])] 
    |   c == d              =   Just pol
    |   otherwise           =   substChar c rest 

substMono :: Mono Char -> Subst -> Maybe (Poly Char)
substMono (0 , []) _ = Just []
substMono (i , []) _ = Just [(i , [])]
substMono (i , c : l) sub = substChar c sub >>= \pol -> substMono (i , l) sub >>= \pal -> Just (timePoly pol pal)

substPoly :: Poly Char -> Subst -> Maybe (Poly Char)
substPoly [] _ = Just []
substPoly (mon : pol) sub = substMono mon sub >>= \pal -> substPoly pol sub >>= \pol' -> Just (plusPoly pal pol')

substExp :: Exp -> Subst -> Maybe Exp
substExp (Pol pol) sub = substPoly pol sub >>= \pal -> Just (Pol pal)

-- substExp (Const i) _ = Just (Const i)
-- substExp (Lin _ _) [] = Nothing
-- substExp (Lin c i) ((d , r) : rest)
--     |   c < d       =   Nothing
--     |   c == d      =   Just (substLin i r)
--     |   otherwise   =   substExp (Lin c i) rest

type Mono a = (Int , [a])   

cleanMono :: Ord a => Mono a -> Mono a
cleanMono (0 , _) = (0 , [])
cleanMono (i , l) = (i , sort l)

timesMono :: Ord a => Mono a -> Mono a -> Mono a
timesMono (i , l) (j , r) = cleanMono (i*j , l ++ r)

type Poly a = [Mono a]

addMono :: Ord a => Mono a -> Poly a -> Poly a
addMono (0 , []) pol = pol
addMono (i , l) [] = [(i , l)]
addMono (i , l) ((j , r) : rest)
    |   l < r       =   (i , l) : (j , r) : rest
    |   l == r      =   (i+j , l) : rest
    |   otherwise   =   (j , r) : addMono (i , l) rest

cleanPoly :: Ord a => Poly a -> Poly a
cleanPoly = foldr (addMono . cleanMono) []

plusPoly :: Ord a => Poly a -> Poly a -> Poly a
plusPoly pol pal = cleanPoly (pol ++ pal)

timePoly :: Ord a => Poly a -> Poly a -> Poly a
timePoly pol pal = cleanPoly [timesMono mon man | mon <- pol , man <- pal]

scalPoly :: Ord a => Int -> Poly a -> Poly a
scalPoly i pol = cleanPoly [(i*j , l) | (j , l) <- pol]

monoPoly :: Ord a => Mono (Poly a) -> Poly a
monoPoly (i , []) = [(i , [])]
monoPoly (i , x : mon) = timePoly x (monoPoly (i , mon))

muPoly :: Ord a => Poly (Poly a) -> Poly a
muPoly = foldr (plusPoly . monoPoly) []

showMono :: Mono Char -> String 
showMono (1 , []) = "1"
showMono (1 , l) = l
showMono (i , l) = show i ++ l

showPoly :: Poly Char -> String 
showPoly [] = "0"
showPoly [mon] = showMono mon 
showPoly (mon : poly) = showMono mon ++ '+' : showPoly poly

minusPoly :: Ord a => Poly a -> Int -> Maybe (Poly a)
minusPoly pol 0 = Just pol
minusPoly [] i 
    |   i <= 0      =   Just []
    |   otherwise   =   Nothing
minusPoly ((j , []) : pol) i
    |   i < j       =   Just ((j-i , []) : pol)
    |   i == j      =   Just pol
    |   otherwise   =   Nothing 
minusPoly _ _ = Nothing

--[(1 , "X") , (1 , "")] 1
----[(1 , "")] 1

--data Polyn = 
--    Con Int 
--    |   Var Char 
--    |   Plus Polyn Polyn
--    |   Times Polyn Polyn

--sortPolyn :: Polyn -> Polyn 
--sortPolyn (Plus (Con i) (Con j)) = Con (i+j)
--sortPolyn (Plus a (Con 0)) = sortPolyn a
--sortPolyn (Plus (Plus a b) c) = sortPolyn (Plus a (Plus b c))
