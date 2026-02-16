module Par where

-- standard libraries
import Data.Bifunctor

-- project libraries
import Morph

-- ============================================================
-- Module for datatype containing all relations between objects
-- ============================================================
-- Implements a preorder as a partial order of equivalence classes

type Set a = [a]

type Par a = [(Set a , Set Int)]
-- Elements consist of an equivalence class together with pointers to element above them < 
-- 1: Each equivalence class and set of pointers are given by an orderered non-repeating set
-- 2: Each equivalence class is distinct
-- 3: Pointers are closed under transitivity, but do not contain a pointer to itself





addClass :: Set a -> Par a -> Par a
addClass l dag = dag ++ [(l , [])]


-- delete class from list, removing all references to it.
delClass :: Int -> Par a -> Par a
delClass i = delClass' i i

delClass' :: Int -> Int -> Par a -> Par a
delClass' _ _ [] = []
delClass' i j ((cla , point) : l)
    |   j == 0      =   delClass' i (j-1) l
    |   otherwise   =   (cla , delPointer i point) : delClass' i (j-1) l

delPointer :: Int -> Set Int -> Set Int
delPointer _ [] = []
delPointer i (j : l)
    |   i < j       =   (j-1) : delPointer i l
    |   i == j      =   delPointer i l
    |   otherwise   =   j : delPointer i l

-- swap two classes
swapClass :: Int -> Int -> Par a -> Par a
swapClass i j par =
    let par' = fmap (second (swapPoint i j)) par in
    let (a , b) = (lookClass i par' , lookClass j par') in
        putList i b (putList j a par')

swapPoint :: Int -> Int -> Set Int -> Set Int
swapPoint _ _ [] = []
swapPoint i j (k : l)
    |   i == k      =   j : swapPoint i j l
    |   j == k      =   i : swapPoint i j l
    |   otherwise   =   k : swapPoint i j l

putList :: Int -> a -> [a] -> [a]
putList _ _ [] = []
putList i x (p : r)
    |   i <= 0      =   x : r
    |   otherwise   =   p : putList (i-1) x r

-- Lookup class
lookClass :: Int -> Par a -> (Set a , Set Int)
lookClass _ [] = ([] , [])
lookClass _ [a] = a
lookClass i (a : l)
    |   i <= 0      =   a
    |   otherwise   =   lookClass (i-1) l


-- Add more elements to a class
addToClass :: Ord a => Set a -> Int -> Par a -> Par a
addToClass x _ [] = [(x , [])]
addToClass x i ((y , p) : l)
    |   i <= 0      =   (joinSet x y , p) : l
    |   otherwise   =   (y , p) : addToClass x (i-1) l

addToPoint :: Ord a => Set Int -> Int -> Par a -> Par a
addToPoint _ _ [] = []
addToPoint q i ((y , p) : l)
    |   i <= 0      =   (y , joinSet q p) : l
    |   otherwise   =   (y , p) : addToPoint q (i-1) l



substPoint :: Ord a => Set Int -> Int -> Par a -> Par a
substPoint _ _ [] = []
substPoint q i ((y , p) : l)
    |   inSet i p   =   (y , joinSet q p) : substPoint q i l
    |   otherwise   =   (y , p) : substPoint q i l

-- Merge two classes
mergeClass :: Ord a => Int -> Int -> Par a -> Par a
mergeClass i j par =
    let (_ , ip) = lookClass i par in
    let (jc , jp) = lookClass j par in
        tidyClass
        (delClass j
        (addToClass jc i
        (addToPoint jp i
        (substPoint (addSet i ip) j
        (substPoint jp i par)))))
-- Everything pointing to i must point to jp (everything pointed from j)
-- Everything pointing to j must point to ip (everything pointed from i)
-- i must point to everything pointed from j 
-- class of j must be merged with class from i
-- j must be removed
-- classes need to be checked for cycles and tidied up

-- Add a preorder reletion to database
preClass :: Ord a => Int -> Int -> Par a -> Par a
preClass i j par =
    let (_ , jp) = lookClass j par in
        tidyClass                           -- classes need to be checked for cycles and tidied up
        (addToPoint (addSet j jp) i         -- to pointers of i, add pointer to j, and to everything pointed from j
        (substPoint (addSet j jp) i par))   -- to anything pointing to i, add pointer to j, and to everything pointed from j

-- Check if any selfreferences, and hence cycles, have been created 
tidyCheck :: Par a -> Bool
tidyCheck par = tidyCheck' par 0

tidyCheck' :: Par a -> Int -> Bool
tidyCheck' [] _ = True
tidyCheck' ((_ , p) : l) i
    |   inSet i p       =   False
    |   otherwise       =   tidyCheck' l (i+1)

-- Removes selfpointers
noselfPointer :: Par a -> Par a
noselfPointer = noselfPointer' 0

noselfPointer' :: Int -> Par a -> Par a
noselfPointer' _ [] = []
noselfPointer' i ((c , p) : l) = (c , delSet i p) : noselfPointer' (i+1) l

-- hook a class back into another class. Returns Nothing if nothing got hooked
hookClass :: Int -> Set Int -> Int -> Par a -> Maybe (Int , Int)
hookClass _ _ _ [] = Nothing
hookClass i p j ((_ , q) : l)
    |   inSet j p && inSet i q  =   Just (i , j)
    |   otherwise               =   hookClass i p (j+1) l

allhookClass :: Int -> Par a -> Maybe (Int , Int)
allhookClass _ [] = Nothing
allhookClass i ((_ , p) : l) = case hookClass i p (i+1) l of
    Just k      ->  Just k
    _           ->  allhookClass (i+1) l

-- merges all cyclic dependencies. Removes self references afterwards
sinkerClass :: Ord a => Par a -> Par a
sinkerClass par = case allhookClass 0 par  of
    Just (i , j)    ->  mergeClass i j par
    _               ->  noselfPointer par

tidyClass :: Ord a => Par a -> Par a
tidyClass par
    |   tidyCheck par   =   par
    |   otherwise       =   sinkerClass par


-- general operations
findClass :: Ord a => a -> Par a -> Maybe Int
findClass _ [] = Nothing
findClass a ((c , _) : l)
    |   inSet a c       =   Just 0
    |   otherwise       =   fmap (+ 1) (findClass a l)


addeqClass :: Ord a => (a , a) -> Par a -> Par a
addeqClass (x , y) par = case (findClass x par , findClass y par) of
    (Just i , Just j)   ->  if i == j then par else mergeClass (min i j) (max i j) par
    (Just i , _     )   ->  addToClass [y] i par
    (_      , Just j)   ->  addToClass [x] j par
    (_      , _     )   ->  addClass (sortSet [x , y]) par

addpreClass :: Ord a => (a , a) -> Par a -> Par a
addpreClass (x , y) par = case (findClass x par , findClass y par) of
    (Just i , Just j)   ->  if i == j then par else preClass i j par
    (Just i , _     )   ->  let n = length par in substPoint [n] i (addToPoint [n] i (addClass [y] par))
    (_      , Just j)   ->  let n = length par in
                            let (_ , jp) = lookClass j par in
                                addToPoint (addSet j jp) n (addClass [x] par)
    (_      , _     )   ->  let n = length par in
                                addToPoint [n+1] n (addClass (sortSet [y]) (addClass (sortSet [x]) par))

-- topological sort
findSwap :: Int -> Par a -> Maybe (Int , Int)
findSwap _ []               =   Nothing
findSwap i ((_ , []) : l)   =   findSwap (i+1) l
findSwap i ((_ , j : _) : l)
    |   j < i               =   Just (j , i)
    |   otherwise           =   findSwap (i+1) l

topoSortPar :: Par a -> Par a
topoSortPar par = case findSwap 0 par of
    Just (i , j)    ->  topoSortPar (swapClass i j par)
    _               ->  par

-- 
cleanPar :: Par a -> Par a
cleanPar par = squeezePar (topoSortPar par)

-- squeezing (separate out all unaffiliated equivalence classes)
squeezePar :: Par a -> Par a
squeezePar par = case squeezeSearch par of
    Just i          ->  squeezePar (swapClass i (i+1) par)
    _               ->  par

squeezeSearch :: Par a -> Maybe Int
squeezeSearch = squeezeSearch' False [] 0

squeezeSearch' :: Bool -> Set Int -> Int -> Par a -> Maybe Int
squeezeSearch' _ _ _ [] = Nothing
squeezeSearch' k p i ((_ , []) : l)
    |   k && not (inSet i p)        =   Just (i-1)
    |   otherwise                   =   squeezeSearch' (inSet i p) p (i+1) l
squeezeSearch' _ p i ((_ , q) : l)  =   squeezeSearch' True (joinSet p q) (i+1) l



-- ========================
-- Rewrite rule name search
-- ========================
-- just putting this here


-- Data structure of names: An ordered type a, giving a sorted list of rewrite rules with names
type RuleNames a = [(a , a , String)]

-- Add new rule name. Will overwrite older name
addName :: Ord a => (a , a , String) -> RuleNames a -> RuleNames a
addName p []        =   [p]
addName (x , y , n) ((z , w , m) : l)
    |   x < z       =   (x , y , n) : (z , w , m) : l
    |   x > z       =   (z , w , m) : addName (x , y , n) l
    |   y < w       =   (x , y , n) : (z , w , m) : l
    |   y > w       =   (z , w , m) : addName (x , y , n) l
    |   otherwise   =   (x , y , n) : l

-- Sort rule names
sortName :: Ord a =>  RuleNames a -> RuleNames a
sortName = foldr addName []

-- Extract names relevant to a class
relevantNames :: Ord a => Set a -> RuleNames a -> RuleNames a
relevantNames _ [] = []
relevantNames [] _ = []
relevantNames (z : r) ((x , y , n) : l)
    |   z < x           =   relevantNames r ((x , y , n) : l)
    |   z > x           =   relevantNames (z : r) l
    |   otherwise       =   (x , y , n) : relevantNames (z : r) l

-- name search
type ChainNames a = [(a , [String])]

inChain :: Ord a => a -> ChainNames a -> Bool
inChain x l = inSet x (fmap fst l)

--addChain :: Ord a => (a , [String]) -> ChainNames a -> ChainNames a 
--addChain x l = addSet x l

searchNameChain :: Ord a => a -> RuleNames a -> [(a , [String])]
searchNameChain a rul = searchNameChain' [(a , [])] [(a , [])] rul rul

searchNameChain' :: Ord a => ChainNames a -> ChainNames a -> RuleNames a -> RuleNames a -> ChainNames a
searchNameChain' [] allnam _ _ = allnam 
searchNameChain' (_ : newnam) allnam [] allrul = searchNameChain' newnam allnam allrul allrul 
searchNameChain' ((a , p) : newnam) allnam ((x , y , n) : currul) allrul 
    |   a < x               =   searchNameChain' newnam allnam allrul allrul 
    |   a > x               =   searchNameChain'    ((a , p) : newnam) allnam currul allrul 
    |   inChain y allnam    =   searchNameChain'    ((a , p) : newnam) allnam currul allrul
    |   otherwise           =   searchNameChain'    ((a , p) : newnam ++ [(y , n : p)]) 
                                                    (addSet (y , n : p) allnam) currul allrul 