{-# LANGUAGE InstanceSigs #-}
module Par2 where

import Morph
import Par
import Matcher
import Proof



fromBar :: String -> String
fromBar [] = []
fromBar ('|' : l) = l
fromBar (_ : l) = fromBar l

fromBars :: String -> [String]
fromBars s = let z = fromBar s in
    if z == "" then [] else uptoBar z : fromBars z

countBars :: String -> Float
countBars [] = 0
countBars ('|' : s) = 1 + countBars s
countBars (_ : s) = countBars s

data PStep =
    PRefl
    |   PBase String
    |   PComp [PStep]
    |   PAnti PStep PStep

instance Show PStep where
    show :: PStep -> String
    show PRefl = "refl"
    show (PBase s) = uptoBar s
    show (PComp []) = ""
    show (PComp [a]) = show a
    show (PComp (a : l)) = show a ++ ";" ++ show (PComp l)
    show (PAnti a b) = "{" ++ show a ++ "<>" ++ show b ++ "}"

revPStep :: PStep -> PStep
revPStep PRefl = PRefl
revPStep (PBase s) = PBase s
revPStep (PComp l) = PComp (reverse (fmap revPStep l))
revPStep (PAnti a b) = PAnti (revPStep b) (revPStep a)

compPStep :: PStep -> PStep -> PStep
compPStep PRefl x = x
compPStep (PComp l) (PComp r) = PComp (l ++ r)
compPStep a (PComp r) = PComp (a : r)
compPStep (PComp l) b = PComp (l ++ [b])
compPStep a b = PComp [a , b]

type Rela a = (a , a , MR , PStep , Why)

type Par a = [Rela a]
-- All minimal relations between elements of type a, lexicographically sorted, with name



inPar :: Ord a => (a , a , MR) -> Par a -> Maybe PStep
inPar _ [] = Nothing
inPar (a , b , x) ((c , d , y , t , _) : l)
    |   a < c       =   Nothing
    |   a > c       =   inPar (a , b , x) l
    |   b < d       =   Nothing
    |   b > d       =   inPar (a , b , x) l
    |   orderMR y x =   Just t
    |   otherwise   =   inPar (a , b , x) l



flushPar :: Char -> Par Morph -> Par Morph
flushPar _ [] = []
flushPar c ((m , n , moder , proof , why) : l)
    |   opinMorph c m || opinMorph c n  =   flushPar c l
    |   otherwise                       =   (m , n , moder , proof , why) : flushPar c l

-- New idea, again

-- 1) Type of all relations

addParO :: Ord a => Rela a -> Par a -> Par a
addParO x [] = [x]
addParO (a , b , x , p , w) ((c , d , y , q , v) : l)
    |   a < c       =   (a , b , x , p , w) : (c , d , y , q , v) : l
    |   a > c       =   (c , d , y , q , v) : addParO (a , b , x , p , w) l
    |   b < d       =   (a , b , x , p , w) : (c , d , y , q , v) : l
    |   b > d       =   (c , d , y , q , v) : addParO (a , b , x , p , w) l
    |   orderMR y x =   (c , d , y , q , v) : l
    |   orderMR x y =   (a , b , x , p , w) : l
    |   otherwise   =   (a , b , MEqual , PAnti p q , Lemma) : l

addRelPar :: Ord a => Rela a -> Par a -> Par a
addRelPar (a , b , x , p , w) par = addParO (b , a , reverseMR x , p , w) (addParO (a , b , x , p , w) par)

addRelsPar :: Ord a => Par a -> Par a -> Par a
addRelsPar par' par = foldr addRelPar par par'


addRelatPar :: Relat -> Par Morph -> Par Morph
addRelatPar (x , m , n , s , w) par
    |   m == n      =   par
    |   otherwise   =   addRelPar (cleanMorph m , cleanMorph n , x , PBase s , w) par

addRelatsPar :: [Relat] -> Par Morph -> Par Morph
addRelatsPar rel par = foldl (flip addRelatPar) par rel

-- 2) A reachability type with proof

type Path a = [(a , MR , PStep)]




-- given a new path: check if new in existing paths, return (potentially modified) path and list of paths with added path
addPath :: Ord a => (a , MR , PStep , Why) -> [(a , MR , PStep , Why)] -> Maybe ((a , MR , PStep , Why) , [(a , MR , PStep , Why)])
addPath x [] = Just (x , [x])
addPath (a , x , p , w) ((b , y , q , v) : l)
    |   a < b       =   Just ((a , x , p , w) , (a , x , p , w) : (b , y , q , v) : l)
    |   a > b       =   addPath (a , x , p , w) l >>= \(n , m) -> Just (n , (b , y , q , v) : m)
    |   orderMR y x =   Nothing
    |   orderMR x y =   Just ((a , x , p , w) , (a , x , p , w) : l)
    |   otherwise   =   Just ((a , MEqual , PAnti p q , Lemma) , (a , MEqual , PAnti p q , Lemma) : l)

-- Find all morphisms linked to the argument morphism. Collect rewrite types, and apply antisymmetry when possible
reachPath :: Ord a => Matcher a -> a -> Par a -> [(a , MR , PStep , Why)]
reachPath mat a par = searchPath mat [(a , MEqual , PRefl , Show)] par [(a , MEqual , PRefl , Show)] par

compWhy :: Why -> Why -> Why 
compWhy Show w = w 
compWhy w Show = w
compWhy _ _ = Lemma

searchPath :: Ord a => Matcher a -> [(a , MR , PStep , Why)] -> Par a -> [(a , MR , PStep , Why)] -> Par a -> [(a , MR , PStep , Why)]
-- no more new paths: return all collected paths
searchPath _ allpaths _ [] _ = allpaths
-- no more new connection from current path, go to next path
searchPath mat allpaths histpar (_ : newpaths) [] = searchPath mat allpaths histpar newpaths histpar
searchPath mat allpaths histpar ((a , x , p , w) : newpaths) ((b , c , y , q , v) : curpar) = case mat b a >>= \f -> f c of
    Just c'     ->  if compatMR x y
                    then case addPath (c' , mergeMR x y , compPStep p q , compWhy w v) allpaths of
                        Just (t , r)    ->  searchPath mat r histpar ((a , x , p , w) : newpaths ++ [t]) curpar
                        _               ->  searchPath mat allpaths histpar ((a , x , p , w) : newpaths) curpar
                    else searchPath mat allpaths histpar ((a , x , p , w) : newpaths) curpar
    Nothing     ->  searchPath mat allpaths histpar ((a , x , p , w) : newpaths) curpar


--    |   a < b           =   searchPath mat allpaths histpar newpaths histpar
--    |   a > b           =   searchPath mat allpaths histpar ((a , x , p) : newpaths) curpar
--    |   compatMR x y    =   case addPath (c , mergeMR x y , compPStep p q) allpaths of
--            Just (t , r)    ->  searchPath mat r histpar ((a , x , p) : newpaths ++ [t]) curpar
--            _               ->  searchPath mat allpaths histpar ((a , x , p) : newpaths) curpar
--    |   otherwise       =   searchPath mat allpaths histpar ((a , x , p) : newpaths) curpar


rewPath :: MR -> [(Morph , MR , PStep , Why)] -> [Rew]
rewPath _ [] = []
rewPath x ((_ , _ , PRefl , _) : l) = rewPath x l
rewPath x ((b , y , p , w) : l)
    |   orderMR y x     =   RS y b (show p) w : rewPath x l
    |   otherwise       =   rewPath x l

-- given a morphism, rewrite mode and accessible equations, give all possible rewrites
rewPar :: Morph -> MR -> Par Morph -> [Rew]
rewPar m x par = let t = reachPath matcherMorph m par in RI m : rewPath x t

-- extra 

nextL :: a -> [a] -> a
nextL _ (_ : y : _) = y
nextL x _ = x

lastL :: a -> [a] -> a
lastL x [] = x
lastL _ [y] = y
lastL _ (x : l) = lastL x l

findCycle :: Eq a => a -> [a] -> [a] -> [a]
findCycle _ l [] = l
findCycle m l (n : r)
    |   m == n      =   r ++ l
    |   otherwise   =   findCycle m (l ++ [n]) r

-- Finding the next and the previous morphism
rewrite :: MR -> Par Morph -> Rew -> Morph -> Rew
rewrite moder par cur his = nextL cur (extractRew moder cur his par)


dewrite :: MR -> Par Morph -> Rew -> Morph -> Rew
dewrite moder par cur his = lastL cur (extractRew moder cur his par)

extractRew :: MR -> Rew -> Morph -> Par Morph -> [Rew]
extractRew moder r m par = r : findCycle r [] (extractRew' moder m par)

extractRew' :: MR -> Morph -> Par Morph -> [Rew]
extractRew' x m = rewPar m x

findName :: Par Morph -> Morph -> Morph -> (MR , String , Why)
findName par m n = let rews = extractRew' MEqual m par in
    case findRew' n rews of
        Just p      ->  p
        Nothing     ->  (MEqual , "?" , Axiom)

findRew' :: Morph -> [Rew] -> Maybe (MR , String , Why)
findRew' _ [] = Nothing
findRew' m ((RI _) : l) = findRew' m l
findRew' m ((RS mr n name why) : l)
    |   m == n      =   Just (mr , name , why)
    |   otherwise   =   findRew' m l


-- Equivalence classes
-- addEquiv :: Ord a => a -> a -> [Set a] -> [Set a]

-- equivPar :: Ord a => Par a -> [Set a]
--equivPar 



equivStruc :: Ord a => Par a -> Parq a
equivStruc [] = []
equivStruc ((m , n , MEqual , _ , _) : l) = addeqClass (m , n) (equivStruc l)
equivStruc ((m , n , MLarger , _ , _) : l) = addpreClass (m , n) (equivStruc l)
equivStruc ((m , n , MSmaller , _ , _) : l) = addpreClass (n , m) (equivStruc l)

-- =====================
-- Compositional closure
-- =====================

-- Check if relations are composable
compRela :: Ord a => Rela a -> Rela a -> [Rela a]
compRela (a , b , MSmaller , t , w) (c , d , MSmaller , q , v)
    |   a == d && b == c    =   [(a , b , MEqual , PAnti (revPStep q) (revPStep t) , Lemma)]
    |   b == c              =   [(a , d , MSmaller , compPStep t q , compWhy w v)]
    |   a == d              =   [(c , b , MSmaller , compPStep q t , compWhy w v)]
compRela (a , b , MLarger , t , w) (c , d , MLarger , q , v)
    |   a == d && b == c    =   [(a , b , MEqual , PAnti t q , Lemma)]
    |   b == c              =   [(a , d , MLarger , compPStep t q , compWhy w v)]
    |   a == d              =   [(c , b , MLarger , compPStep q t , compWhy w v)]
compRela (a , b , MEqual , t , w) (c , d , y , q , v)
    |   b == c              =   [(a , d , y , compPStep t q , compWhy w v)]
    |   a == d              =   [(c , b , y , compPStep q t , compWhy w v)]
compRela (a , b , x , t , w) (c , d , MEqual , q , v)
    |   b == c              =   [(a , d , x , compPStep t q , compWhy w v)]
    |   a == d              =   [(c , b , x , compPStep q t , compWhy w v)]
compRela _ _ = []

compPar :: Ord a => Rela a -> Par a -> [Rela a]
compPar _ [] = []
compPar rel (rel' : r) = compRela rel rel' ++ compPar rel r

addPar :: Ord a => Rela a -> Par a -> Par a
addPar (a , b , x , t , w) par
    |   a == b      =   par
    |   otherwise   =   case inPar (a , b , x) par of
    Just _      ->  par
    _           ->
        let par2 = addPar' (b , a , reverseMR x , revPStep t , w) (addPar' (a , b , x , t , w) par) in
        let com = compPar (a , b , x , t , w) par in
            addsPar com par2

addPar' :: Ord a => Rela a -> Par a -> Par a
addPar' (a , b , x , t , w) [] = [(a , b , x , t , w)]
addPar' (a , b , x , r , w) ((c , d , y , t , v) : l)
    |   a < c       =   (a , b , x , r , w) : (c , d , y , t , v) : l
    |   a > c       =   (c , d , y , t , v) :  addPar' (a , b , x , r , w) l
    |   b < d       =   (a , b , x , r , w) : (c , d , y , t , v) : l
    |   b > d       =   (c , d , y , t , v) :  addPar' (a , b , x , r , w) l
    |   orderMR x y =   addPar' (a , b , x , r , w) l
    |   orderMR y x =   (c , d , y , t , v) : l
    |   x < y       =   (a , b , x , r , w) : (c , d , y , t , v) : l
    |   otherwise   =   (c , d , y , t , v) : addPar' (a , b , x , r , w) l
--    |   otherwise   =   (c , d , y , t) : l


addsPar :: Ord a => [Rela a] -> Par a -> Par a
addsPar l par = foldr addPar par l

