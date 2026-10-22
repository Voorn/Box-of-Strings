module Theory.Par where

-- standard libraries

-- project libraries
import Morph



-- ============================================================
-- Module for datatype containing all relations between objects
-- ============================================================
-- Implements a preorder as a partial order of equivalence classes

type Set a = [a]

type Parq a = [(Set a , Set Int)]
-- Elements consist of an equivalence class together with pointers to element above them < 
-- 1: Each equivalence class and set of pointers are given by an orderered non-repeating set
-- 2: Each equivalence class is distinct
-- 3: Pointers are closed under transitivity, but do not contain a pointer to itself





addClass :: Set a -> Parq a -> Parq a
addClass l dag = dag ++ [(l , [])]


-- delete class from list, removing all references to it.
delClass :: Int -> Parq a -> Parq a
delClass i = delClass' i i

delClass' :: Int -> Int -> Parq a -> Parq a
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


-- Lookup class
lookClass :: Int -> Parq a -> (Set a , Set Int)
lookClass _ [] = ([] , [])
lookClass _ [a] = a
lookClass i (a : l)
    |   i <= 0      =   a
    |   otherwise   =   lookClass (i-1) l


-- Add more elements to a class
addToClass :: Ord a => Set a -> Int -> Parq a -> Parq a
addToClass x _ [] = [(x , [])]
addToClass x i ((y , p) : l)
    |   i <= 0      =   (joinSet x y , p) : l
    |   otherwise   =   (y , p) : addToClass x (i-1) l

addToPoint :: Ord a => Set Int -> Int -> Parq a -> Parq a
addToPoint _ _ [] = []
addToPoint q i ((y , p) : l)
    |   i <= 0      =   (y , joinSet q p) : l
    |   otherwise   =   (y , p) : addToPoint q (i-1) l



substPoint :: Ord a => Set Int -> Int -> Parq a -> Parq a
substPoint _ _ [] = []
substPoint q i ((y , p) : l)
    |   inSet i p   =   (y , joinSet q p) : substPoint q i l
    |   otherwise   =   (y , p) : substPoint q i l

-- Merge two classes
mergeClass :: Ord a => Int -> Int -> Parq a -> Parq a
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
preClass :: Ord a => Int -> Int -> Parq a -> Parq a
preClass i j par =
    let (_ , jp) = lookClass j par in
        tidyClass                           -- classes need to be checked for cycles and tidied up
        (addToPoint (addSet j jp) i         -- to pointers of i, add pointer to j, and to everything pointed from j
        (substPoint (addSet j jp) i par))   -- to anything pointing to i, add pointer to j, and to everything pointed from j

-- Check if any selfreferences, and hence cycles, have been created 
tidyCheck :: Parq a -> Bool
tidyCheck par = tidyCheck' par 0

tidyCheck' :: Parq a -> Int -> Bool
tidyCheck' [] _ = True
tidyCheck' ((_ , p) : l) i
    |   inSet i p       =   False
    |   otherwise       =   tidyCheck' l (i+1)

-- Removes selfpointers
noselfPointer :: Parq a -> Parq a
noselfPointer = noselfPointer' 0

noselfPointer' :: Int -> Parq a -> Parq a
noselfPointer' _ [] = []
noselfPointer' i ((c , p) : l) = (c , delSet i p) : noselfPointer' (i+1) l

-- hook a class back into another class. Returns Nothing if nothing got hooked
hookClass :: Int -> Set Int -> Int -> Parq a -> Maybe (Int , Int)
hookClass _ _ _ [] = Nothing
hookClass i p j ((_ , q) : l)
    |   inSet j p && inSet i q  =   Just (i , j)
    |   otherwise               =   hookClass i p (j+1) l

allhookClass :: Int -> Parq a -> Maybe (Int , Int)
allhookClass _ [] = Nothing
allhookClass i ((_ , p) : l) = case hookClass i p (i+1) l of
    Just k      ->  Just k
    _           ->  allhookClass (i+1) l

-- merges all cyclic dependencies. Removes self references afterwards
sinkerClass :: Ord a => Parq a -> Parq a
sinkerClass par = case allhookClass 0 par  of
    Just (i , j)    ->  mergeClass i j par
    _               ->  noselfPointer par

tidyClass :: Ord a => Parq a -> Parq a
tidyClass par
    |   tidyCheck par   =   par
    |   otherwise       =   sinkerClass par


-- general operations
findClass :: Ord a => a -> Parq a -> Maybe Int
findClass _ [] = Nothing
findClass a ((c , _) : l)
    |   inSet a c       =   Just 0
    |   otherwise       =   fmap (+ 1) (findClass a l)


addeqClass :: Ord a => (a , a) -> Parq a -> Parq a
addeqClass (x , y) par = case (findClass x par , findClass y par) of
    (Just i , Just j)   ->  if i == j then par else mergeClass (min i j) (max i j) par
    (Just i , _     )   ->  addToClass [y] i par
    (_      , Just j)   ->  addToClass [x] j par
    (_      , _     )   ->  addClass (sortSet [x , y]) par

addpreClass :: Ord a => (a , a) -> Parq a -> Parq a
addpreClass (x , y) par = case (findClass x par , findClass y par) of
    (Just i , Just j)   ->  if i == j then par else preClass i j par
    (Just i , _     )   ->  let n = length par in substPoint [n] i (addToPoint [n] i (addClass [y] par))
    (_      , Just j)   ->  let n = length par in
                            let (_ , jp) = lookClass j par in
                                addToPoint (addSet j jp) n (addClass [x] par)
    (_      , _     )   ->  let n = length par in
                                addToPoint [n+1] n (addClass (sortSet [y]) (addClass (sortSet [x]) par))

