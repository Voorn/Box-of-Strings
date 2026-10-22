{-# LANGUAGE InstanceSigs #-}
module Theory.Matcher where

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


newtype Exp b = Pol (Poly b Char) 
    deriving (Eq , Ord)

constExp :: (Eq b , Num b) => b -> Exp b
constExp 0 = Pol []
constExp i = Pol [(i , [])]

linExp :: (Eq b , Num b) => Char -> b -> Exp b 
linExp c 0 = Pol [(1 , [c])]
linExp c i = Pol [(i , []) , (1 , [c])]

instance (Eq b , Num b , Show b) => Show (Exp b) where
    show :: Exp b -> String
    show (Pol pol) = showPoly pol

smallLet :: Char -> Bool
smallLet c  = inList c "abcdefghijklmnopqrstuvwxyz"

bigLet :: Char -> Bool
bigLet c    = inList c "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

type Subst b = [(Char , Exp b)]

addSubst :: (Char , Exp b) -> Subst b -> Maybe (Subst b)
addSubst x [] = Just [x]
addSubst (c , l) ((d , r) : rest)
    |   c < d       =   Just ((c , l) : (d , r) : rest)
    |   c > d       =   fmap ((d , r) :) (addSubst (c , l) rest)
    |   otherwise   =   Nothing

addSubsts :: Subst b -> Subst b -> Maybe (Subst b)
addSubsts [] sub = Just sub
addSubsts (x : dub) sub = addSubsts dub sub >>= \rub -> addSubst x rub

matchExp :: (Ord b , Num b) => Exp b -> Exp b -> Maybe (Subst b)
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


substChar :: (Eq b , Num b) => Char -> Subst b -> Maybe (Poly b Char)
substChar c []
    |   bigLet c    =   Nothing 
    |   otherwise   =   Just [(1 , [c])]
substChar c ((d , Pol pol) : rest)
    |   c < d && bigLet c   =   Nothing 
    |   c < d               =   Just [(1 , [c])] 
    |   c == d              =   Just pol
    |   otherwise           =   substChar c rest 

substMono :: (Eq b , Num b) => Mono b Char -> Subst b -> Maybe (Poly b Char)
substMono (0 , []) _ = Just []
substMono (i , []) _ = Just [(i , [])]
substMono (i , c : l) sub = substChar c sub >>= \pol -> substMono (i , l) sub >>= \pal -> Just (timePoly pol pal)

substPoly :: (Eq b , Num b) => Poly b Char -> Subst b -> Maybe (Poly b Char)
substPoly [] _ = Just []
substPoly (mon : pol) sub = substMono mon sub >>= \pal -> substPoly pol sub >>= \pol' -> Just (plusPoly pal pol')

substExp :: (Eq b , Num b) => Exp b -> Subst b -> Maybe (Exp b)
substExp (Pol pol) sub = substPoly pol sub >>= \pal -> Just (Pol pal)

-- substExp (Const i) _ = Just (Const i)
-- substExp (Lin _ _) [] = Nothing
-- substExp (Lin c i) ((d , r) : rest)
--     |   c < d       =   Nothing
--     |   c == d      =   Just (substLin i r)
--     |   otherwise   =   substExp (Lin c i) rest

type Mono b a = (b , [a])   

cleanMono :: (Eq b , Num b , Ord a) => Mono b a -> Mono b a
cleanMono (0 , _) = (0 , [])
cleanMono (i , l) = (i , sort l)

timesMono :: (Eq b , Num b , Ord a) => Mono b a -> Mono b a -> Mono b a
timesMono (i , l) (j , r) = cleanMono (i*j , l ++ r)

type Poly b a = [Mono b a]

addMono :: (Eq b , Num b , Ord a) => Mono b a -> Poly b a -> Poly b a
addMono (0 , []) pol = pol
addMono (i , l) [] = [(i , l)]
addMono (i , l) ((j , r) : rest)
    |   l < r       =   (i , l) : (j , r) : rest
    |   l == r      =   (i+j , l) : rest
    |   otherwise   =   (j , r) : addMono (i , l) rest

cleanPoly :: (Eq b , Num b , Ord a) => Poly b a -> Poly b a
cleanPoly = foldr (addMono . cleanMono) []

plusPoly :: (Eq b , Num b , Ord a) => Poly b a -> Poly b a -> Poly b a
plusPoly pol pal = cleanPoly (pol ++ pal)

timePoly :: (Eq b , Num b , Ord a) => Poly b a -> Poly b a -> Poly b a
timePoly pol pal = cleanPoly [timesMono mon man | mon <- pol , man <- pal]

scalPoly :: (Eq b , Num b , Ord a) => b -> Poly b a -> Poly b a
scalPoly i pol = cleanPoly [(i*j , l) | (j , l) <- pol]

monoPoly :: (Eq b , Num b , Ord a) => Mono b (Poly b a) -> Poly b a
monoPoly (i , []) = [(i , [])]
monoPoly (i , x : mon) = timePoly x (monoPoly (i , mon))

muPoly :: (Eq b , Num b , Ord a) => Poly b (Poly b a) -> Poly b a
muPoly = foldr (plusPoly . monoPoly) []

showMono :: (Eq b , Num b , Show b) => Mono b Char -> String 
showMono (1 , []) = "1"
showMono (1 , l) = l
showMono (i , l) = show i ++ l

showPoly :: (Eq b , Num b , Show b) => Poly b Char -> String 
showPoly [] = "0"
showPoly [mon] = showMono mon 
showPoly (mon : poly) = showMono mon ++ '+' : showPoly poly

minusPoly :: (Ord b , Num b , Ord a) => Poly b a -> b -> Maybe (Poly b a)
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
