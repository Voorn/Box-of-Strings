module Rewrite where

-- standard library
import Data.Maybe

-- project libraries
import Morph
import Par

-- =============================
-- Rewrite rules and theory
-- =============================

-- addRelats :: [Relat] -> [[Morph]] -> [[Morph]]
-- addRelats [] equiv = equiv
-- addRelats (Equ m n : relat) equiv = addEquiv (insertSort m , insertSort n) (addRelats relat equiv)
-- addRelats (Pre {} : relat) equiv = addRelats relat equiv
-- addRelats (Erp {} : relat) equiv = addRelats relat equiv


addrelClass :: [Relat] -> Par Morph -> Par Morph
addrelClass [] par = par
addrelClass ((MEqual , m , n)   : relat) par    = addeqClass (cleanMorph m , cleanMorph n) (addrelClass relat par)
addrelClass ((MLarger , m , n)  : relat) par    = addpreClass (cleanMorph m , cleanMorph n) (addrelClass relat par)
addrelClass ((MSmaller , m , n) : relat) par    = addpreClass (cleanMorph n , cleanMorph m) (addrelClass relat par)


-- Generate equivalence classes from equations
addEquiv :: (Morph , Morph) -> [[Morph]] -> [[Morph]]
addEquiv (m , n) [] = [addSet m [n]]
addEquiv (m , n) (s : l)
    |   inSet m s       =   addSet n s : l
    |   inSet n s       =   addSet m s : l
    |   otherwise       =   s : addEquiv (m , n) l

genEquiv :: [(Morph , Morph)] -> [[Morph]]
genEquiv = foldr addEquiv []

cleanEquiv :: Ord a => [[a]] -> [[a]]
cleanEquiv v = reverse (foldr (addClass' . sortSet) [] v)

addClass' :: Ord a => [a] -> [[a]] -> [[a]]
addClass' l [] = [l]
addClass' l (r : v)
    |   intSet l r      =   addClass' (joinSet l r) v
    |   otherwise       =   r : addClass' l v

-- Extract equations from equivalence classes 
rewriteClean :: [[Morph]] -> [(Morph , Morph)]
rewriteClean x = rewriteExp (genEquiv (rewriteExp x))

rewriteExp :: [[Morph]] -> [(Morph , Morph)]
rewriteExp [] = []
rewriteExp ([] : l) = rewriteExp l
rewriteExp ([_] : l) = rewriteExp l
rewriteExp ((a : b : x) : l) = (a , b) : rewriteExp' a (b : x) ++ rewriteExp l

rewriteExp' :: Morph -> [Morph] -> [(Morph , Morph)]
rewriteExp' _ [] = []
rewriteExp' first [m] = [(m , first)]
rewriteExp' first (m : n : l) = (m , n) : rewriteExp' first (n : l)


nextL :: a -> [a] -> a
nextL _ (_ : y : _) = y
nextL x _ = x

lastL :: a -> [a] -> a
lastL x [] = x
lastL _ [y] = y
lastL _ (x : l) = lastL x l

-- Finding the next and the previous morphism
rewrite :: MR -> Par Morph -> Rew -> Morph -> Rew
rewrite moder par cur his = nextL cur (extractRew moder cur his par)
    --case poppers m rew of
    --Just (_ , x)    ->  x
    --_               ->  m

dewrite :: MR -> Par Morph -> Rew -> Morph -> Rew
dewrite moder par cur his = lastL cur (extractRew moder cur his par)


rewrite' :: Morph -> [(Morph , Morph)] -> Morph
rewrite' m [] = m
rewrite' m ((n , p) : l)
    |   m == n      =   p
    |   otherwise   =   rewrite' m l

--dewrite :: [[Morph]] -> Morph -> Morph
--dewrite rew m = case poppers m rew of
--    Just (x , _)    ->  x
--    _               ->  m

dewrite' :: Morph -> [(Morph , Morph)] -> Morph
dewrite' m [] = m
dewrite' m ((n , p) : l)
    |   m == p      =   n
    |   otherwise   =   dewrite' m l

laster :: a -> [a] -> a
laster x [] = x
laster _ [y] = y
laster _ (y : l) = laster y l

firster :: a -> [a] -> a
firster x [] = x
firster _ (y : _) = y

poppers :: Eq a => a -> [[a]] -> Maybe (a , a)
poppers _ []        =   Nothing
poppers a (x : l)   =   case popper a x of
    Just y          ->  Just y
    Nothing         ->  poppers a l

popper :: Eq a => a -> [a] -> Maybe (a , a)
popper a (b : r)    =   popper' a [] b r
popper _ _          =   Nothing

popper' :: Eq a => a -> [a] -> a -> [a] -> Maybe (a , a)
popper' _ [] _ []       =   Nothing
popper' a l b []
    |   a == b      =   Just (firster b l , laster b l)
    |   otherwise   =   Nothing
popper' a l b (c : r)
    |   a == b      =   Just (c , laster c (r ++ l))
    |   otherwise   =   popper' a (l ++ [b]) c r



extractRew :: MR -> Rew -> Morph -> Par Morph -> [Rew]
extractRew moder r m par = r : findCycle r [] (extractRew' moder m par)

extractRew' :: MR -> Morph -> Par Morph -> [Rew]
extractRew' MEqual m par =
    let (cla , _ , _) = findClassI m par in
        RI m : fmap (RS MEqual) (findCycle m [] cla)
extractRew' MLarger m par =
    let (cla , poi , _) = findClassI m par in
        RI m : fmap (RS MEqual) (findCycle m [] cla) ++ fmap (RS MLarger) (allPoint par poi)
extractRew' MSmaller m par =
    let (cla , _ , i) = findClassI m par in
        RI m : fmap (RS MEqual) (findCycle m [] cla) ++ fmap (RS MSmaller) (llaPoint par i)

allPoint :: Par a -> Set Int -> [a]
allPoint _ [] = []
allPoint par (i : l) = fst (lookClass i par) ++ allPoint par l

llaPoint :: Par a -> Int -> [a]
llaPoint [] _ = []
llaPoint ((s , p) : r) i
    |   inSet i p   =   s ++ llaPoint r i
    |   otherwise   =   llaPoint r i

findCycle :: Eq a => a -> [a] -> [a] -> [a]
findCycle _ l [] = l
findCycle m l (n : r)
    |   m == n      =   r ++ l
    |   otherwise   =   findCycle m (l ++ [n]) r

findClassI :: Ord a => a -> Par a -> (Set a , Set Int , Int)
findClassI _ [] = ([] , [] , 0)
findClassI a ((s , p) : l)
    |   inSet a s   =   (s , p , 0)
    |   otherwise   =   let (x , y , z) = findClassI a l in (x , y , z+1)





equivPop :: Eq a => a -> [a] -> [[a]] -> [a]
equivPop _ _ [] = []
equivPop m _ ([] : l) = equivPop m [] l
equivPop m r ((x : l) : w)
    |   m == x          =   l ++ r
    |   otherwise       =   equivPop m (r ++ [x]) (l : w)


-- =========================================
-- Modifications: For type editing morphisms
-- =========================================

removeLast :: Morph -> Morph
removeLast (Start i) = Start i
removeLast (Op m _ _) = m

downLast :: Morph -> Morph
downLast (Start i) = Start i
downLast (Op m i o)  =
    let (_ , b) = typeMorph m in
    let (c , _) = typeOper o  in
        if (i+1+c) <= b then Op m (i+1) o else Op m i o

upLast :: Morph -> Morph
upLast (Start i) = Start i
upLast (Op m i o)
    |   i > 0       =   Op m (i-1) o
    |   otherwise   =   Op m i o


signatMorph :: [Sig] -> Morph -> [Sig]
signatMorph l (Start _) = l
signatMorph l (Op m _ (Base (Sig f x i j))) = signatMorph (addSet (Sig f x i j) l) m
signatMorph l (Op m _ _) = signatMorph l m

signatEquiv :: [Sig] -> [Morph] -> [Sig]
signatEquiv l [] = l
signatEquiv l (m : r) = signatMorph (signatEquiv l r) m

findMorph :: [Sig] -> Char -> Maybe Sig
findMorph [] _ = Nothing
findMorph ((Sig d s i j) : l) c
    |   c == d          =   Just (Sig d s i j)
    |   otherwise       =   findMorph l c
--findMorph (_ : l) c =   findMorph l c

addOper :: Sig -> Morph -> Morph
addOper (Sig f fs i j) m =
    let (_ , b) = typeMorph m in
        if i <= b then Op m 0 (Base (Sig f fs i j)) else m

inpOper :: Int -> Morph -> Morph
inpOper i (Op m j (Base (Sig f x a b)))  =
    let (_ , mo) = typeMorph m in if (j + i) <= mo then Op m j (Base (Sig f x i b)) else Op m j (Base (Sig f x a b))
inpOper _ m = m

outOper :: Int -> Morph -> Morph
outOper i (Op m j (Base (Sig f x a _)))  =   Op m j (Base (Sig f x a i))
outOper _ m = m

extraWire :: Morph -> Morph
extraWire (Start i) = Start (i+1)
extraWire (Op m i o) = Op (extraWire m) i o

removeWire :: Morph -> Morph
removeWire (Start i) = Start (max 0 (i-1))
removeWire (Op m i o) =
    let (oi , _) = typeOper o in
    let (_ , mo) = typeMorph m in
        if (i + oi) < mo then Op (removeWire m) i o else Op m i o

showEquiv :: [[Morph]] -> String
showEquiv [] = ""
showEquiv ([] : l) = "\n\n" ++ showEquiv l
showEquiv ([m] : l) = show m ++ "\n\n" ++ showEquiv l
showEquiv ((m : r) : l) = show m ++ "\n= " ++ showEquiv (r : l)

-- ===================
-- Automatic rewriting
-- ===================

-- all possible starts to a morphism
firstMorph :: Morph -> [Morph]
firstMorph (Start _) = []
firstMorph (Op m i o) =
    let l = m : firstMorph m in
        mapMaybe swapMorph (fmap (\n -> Op n i o) l)

-- trying to swap the first two Options
swapMorph :: Morph -> Maybe Morph
swapMorph (Op (Op m j q) i o) =
    let (oi , oo) = typeOper o in
    let (qi , qo) = typeOper q in
    if (j + qo) <= i then
        Just (Op (Op m (i-qo+qi) o) j q)
    else
        if (i + oi) <= j then
            Just (Op (Op m i o) (j-oi+oo) q)
        else
            Nothing
swapMorph _ = Nothing

popMorph :: Morph -> Maybe (Int , Oper , Morph)
popMorph (Op m i o) = Just (i , o , m)
popMorph _ = Nothing

-- any possible morphism (caveate: doesn't work well with units and counit stuff)
anyMorph :: Morph -> [Morph]
anyMorph (Start i) = [Start i]
anyMorph m =
    let l = m : firstMorph m in
    let r = mapMaybe popMorph l in
        concat [[Op v i o | v <- anyMorph n] | (i , o , n) <- r]


-- trying to match the first two Options
matchMorph :: Morph -> Morph -> ([(Int , Oper)] , Morph , Morph)
matchMorph (Start i) n = ([] ,  Start i , n)
matchMorph m (Start j) = ([] ,  m , Start j)
matchMorph (Op m i o) (Op n j q)
    |   i == j && o == q    =   let (l , m' , n') = matchMorph m n in ((i , o) : l , m' , n')
    |   otherwise           =   ([] , Op m i o , Op n j q)



stripMorph :: Morph -> Int -> [(Int , Oper , Int)]
stripMorph (Start _) _ = []
stripMorph (Op m i o) k = (i , o , k) : stripMorph m (k+1)

swapStrip ::[(Int , Oper , Int)] -> Maybe [(Int , Oper , Int)]
swapStrip ((i , o , a) : (j , q , b) : l) =
    let (oi , oo) = typeOper o in
    let (qi , qo) = typeOper q in
    if (j + qo) <= i then
        Just ((j , q , b) : (i-qo+qi , o , a) : l)
    else
        if (i + oi) <= j then
            Just ((j-oi+oo , q , b) : (i , o , a) : l)
        else
            Nothing
swapStrip _ = Nothing

firstStrip :: [(Int , Oper , Int)] -> [[(Int , Oper , Int)]]
firstStrip [] = []
firstStrip ((i , o , a) : l) =
    let v = l : firstStrip l in
        mapMaybe (swapStrip . ((i , o , a) :)) v

swapStripD ::[(Int , Oper , Int)] -> Maybe [(Int , Oper , Int)]
swapStripD ((j , q , b) : (i , o , a) : l) =
    let (oi , oo) = typeOper o in
    let (qi , qo) = typeOper q in
    if (j + qo) <= i then
        Just ((i-qo+qi , o , a) : (j , q , b) : l)
    else
        if (i + oi) <= j then
            Just ((i , o , a) : (j-oi+oo , q , b) : l)
        else
            Nothing
swapStripD _ = Nothing

firstStripD :: [(Int , Oper , Int)] -> [[(Int , Oper , Int)]]
firstStripD [] = []
firstStripD ((i , o , a) : l) =
    let v = l : firstStripD l in
        mapMaybe (swapStripD . ((i , o , a) :)) v

matchStrip :: [(Int , Oper , Int)] -> [(Int , Oper , Int)] -> Maybe ((Int , Oper , Int , Int) , [(Int , Oper , Int)] , [(Int , Oper , Int)])
matchStrip _ [] = Nothing
matchStrip [] _ = Nothing
matchStrip ((i , o , a) : l) ((j , q , b) : r)
    |   i == j && o == q        =   Just ((i , o , a , b) , l , r)
    |   otherwise               =   Nothing

matchStripS :: [(Int , Oper , Int)] -> [(Int , Oper , Int)] -> ([(Int , Oper , Int , Int)] , [(Int , Oper , Int)] , [(Int , Oper , Int)])
matchStripS [] r                =   ([] , [] , r)
matchStripS l []                =   ([] , l , [])
matchStripS l r                 =   case matchStrip l r of
                                        Just ((i , o , a , b) , l' , r')   ->  let (x , y , z) = matchStripS l' r' in ((i , o , a , b) : x , y , z)
                                        Nothing                 ->  ([] , l , r)

matchStrip2 :: [(Int , Oper , Int)] -> [(Int , Oper , Int)] -> ([(Int , Oper , Int , Int)] , [(Int , Oper , Int)] , [(Int , Oper , Int)])
matchStrip2 [] r                =   ([] , [] , r)
matchStrip2 l []                =   ([] , l , [])
matchStrip2 l r                 =   let v = l : firstStrip l in
                                    let w = r : firstStrip r in
                                    case tryAny (uncurry matchStrip) [(x , y) | x <- v , y <- w] of
                                        Just ((i , o , a , b) , l' , r')   ->  let (x , y , z) = matchStrip2 l' r' in ((i , o , a , b) : x , y , z)
                                        Nothing                 ->  ([] , l , r)

matchStrip2D :: [(Int , Oper , Int)] -> [(Int , Oper , Int)] -> ([(Int , Oper , Int , Int)] , [(Int , Oper , Int)] , [(Int , Oper , Int)])
matchStrip2D [] r               =   ([] , [] , r)
matchStrip2D l []               =   ([] , l , [])
matchStrip2D l r                =   let v = l : firstStripD l in
                                    let w = r : firstStripD r in
                                    case tryAny (uncurry matchStrip) [(x , y) | x <- v , y <- w] of
                                        Just ((i , o , a , b) , l' , r')    ->  let (x , y , z) = matchStrip2D l' r' in ((i , o , a , b) : x , y , z)
                                        Nothing                             ->  ([] , l , r)


matchGo :: [(Int , Oper , Int)] -> [(Int , Oper , Int)] -> ([(Int , Oper , Int , Int)] , [(Int , Oper , Int , Int)] , [(Int , Oper , Int)] , [(Int , Oper , Int)])
matchGo l r =   let (fir1 , l1 , r1) = matchStripS l r in
                let (las2 , l2 , r2) = matchStripS (reverse l1) (reverse r1) in
                let (las3 , l3 , r3) = matchStrip2D l2 r2 in
                let (fir4 , l4 , r4) = matchStrip2 (reverse l3) (reverse r3) in
                    (fir1 ++ fir4 , reverse las3 ++ reverse las2 , l4 , r4)

foldGo :: Int -> ([(Int , Oper , Int , Int)] , [(Int , Oper , Int , Int)] , [(Int , Oper , Int)] , [(Int , Oper , Int)]) -> (Morph , Morph)
foldGo i (fir , las , l , r) =
    let (a , m , n) = subStrips l r in
    (foldMorph i (fmap (\(x , y , _ , _) -> (x , y)) fir ++ (a , Comp (RS MEqual m) m) : fmap (\(x , y , _ , _) -> (x , y)) las) ,
     foldMorph i (fmap (\(x , y , _ , _) -> (x , y)) fir ++ (a , Comp (RS MEqual n) n) : fmap (\(x , y , _ , _) -> (x , y)) las))

permGo :: ([(Int , Oper , Int , Int)] , [(Int , Oper , Int , Int)] , [(Int , Oper , Int)] , [(Int , Oper , Int)]) -> ([Int] , [Int])
permGo (fir , las , m , n) = (  fmap (\(_ , _ , z , _) -> z) fir ++ fmap (\(_ , _ , z) -> z) m ++ fmap (\(_ , _ , z , _) -> z) las ,
                                fmap (\(_ , _ , _ , z) -> z) fir ++ fmap (\(_ , _ , z) -> z) n ++ fmap (\(_ , _ , _ , z) -> z) las)

permZip :: Int -> Int -> [Int] -> [a] -> [(Int , a)]
permZip _ _ _ [] = []
permZip _ _ [] _ = []
permZip i j (a : l) (b : r)
    |   i <= 0 && j <= 0    =   zip (a : l) r
    |   i <= 0              =   (a , b) : permZip 0 (j-1) l (b : r)
    |   otherwise           =   (a , b) : permZip (i-1) j l r

permCoor :: Int -> Int -> [Int] -> [(Float , Float)] -> [(Float , Float)]
permCoor i j x y = fmap snd (sortSet (permZip i j x y))

coorGo :: Int -> ([(Int , Oper , Int , Int)] , [(Int , Oper , Int , Int)] , [(Int , Oper , Int)] , [(Int , Oper , Int)]) -> ([(Float , Float)] , [(Float , Float)])
coorGo i (fir , las , l , r) =
    let (m , n) = foldGo i (fir , las , l , r) in
    let (p , q) = permGo (fir , las , l , r) in
    let (a , b , c) = (length fir , length l , length r) in
        (permCoor a b p (coorMorph m) , permCoor a c q (coorMorph n))

-- coordinates for transition
transCoor :: Morph -> Morph -> ([(Float , Float)] , [(Float , Float)])
transCoor m n =
    let (mi , _) = typeMorph m in
    let t = matchGo (stripMorph m 0) (stripMorph n 0) in
        coorGo mi t


foldMorph :: Int -> [(Int , Oper)] -> Morph
foldMorph i [] = Start i
foldMorph i ((j , o) : l) = Op (foldMorph i l) j o

typeStrip' :: [(Int , Oper , Int)] -> (Int , Int , Int)
typeStrip' [] = (0 , 0 , 0)
typeStrip' [(i , o , _)] = let (oi , oo) = typeOper o in (i , i + oi , i + oo)
typeStrip' ((i , o , _) : l) =
    let (oi , oo) = typeOper o in
    let (x , y , z) = typeStrip' l in (min x i , max y (i + oi - z + y) , max (z - oi + oo) (i + oo))


subStrips :: [(Int , Oper , Int)] -> [(Int , Oper , Int)] -> (Int , Morph , Morph)
subStrips l r = let (x , y , _) = typeStrip' l in
                let (x' , y' , _) = typeStrip' r in
                let (v , w) = (min x x' , max y y') in
                let m = foldMorph (w-v) (fmap (\(a , b , _) -> (a-x , b)) l) in
                let n = foldMorph (w-v) (fmap (\(a , b , _) -> (a-v , b)) r) in
                    (v , m , n)
