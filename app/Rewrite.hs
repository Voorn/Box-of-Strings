module Rewrite where

-- standard library
import Data.Maybe

-- project libraries
import Morph


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
    (foldMorph i (fmap (\(x , y , _ , _) -> (x , y)) fir ++ (a , Comp (RI m) m) : fmap (\(x , y , _ , _) -> (x , y)) las) ,
     foldMorph i (fmap (\(x , y , _ , _) -> (x , y)) fir ++ (a , Comp (RI n) n) : fmap (\(x , y , _ , _) -> (x , y)) las))

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

coorGo :: Int -> ([(Int , Oper , Int , Int)] , [(Int , Oper , Int , Int)] , [(Int , Oper , Int)] , [(Int , Oper , Int)]) 
    -> ([(Float , Float)] , [(Float , Float)])
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



-- =================================
-- || ANIMATION: COORDINATE STUFF ||
-- =================================

-- permuter function 
type Perm = [ Int ]

applyPerm :: a -> Perm -> [a] -> [a]
applyPerm _ [] _ = []
applyPerm a (i : p) l = lookList i a l : applyPerm a p l

applyPermCoor :: Perm -> [(Float , Float , Bool)] -> [(Float , Float , Bool)]
applyPermCoor p coor = applyPerm (0 , 0 , False) (reverse p) (reverse coor)

compPerm :: Perm -> Perm -> Perm 
compPerm p q = applyPerm 0 q p 

-- invers permutation function
reversePerm :: Perm -> Perm 
reversePerm p = reversePerm' p 0 p 

reversePerm' :: Perm -> Int -> Perm -> Perm 
reversePerm' [] _ p = p
reversePerm' (i : q) j p = reversePerm' q (j+1) (updateList i j p)




keepSortMorph :: Morph -> [(Float, Float , Bool)] -> (Morph , [(Float, Float , Bool)])
keepSortMorph m l = let (n , perm) = sortMall m in 
    (n , applyPerm (0 , 0 , False) perm (reverse l))

keepMatchMorph :: Morph -> Morph -> Perm
keepMatchMorph m n = 
    let (_ , perm) = sortMall m in 
    let (_ , pern) = sortMall n in 
        compPerm (reverse perm) (reversePerm (reverse pern))

keepMatchCoor :: Morph -> Morph -> [(Float, Float , Bool)] -> [(Float, Float , Bool)]
keepMatchCoor m n coor = 
    let perm = keepMatchMorph m n in
        applyPermCoor perm coor


-- box coordinate function
boxCoorPre :: Morph -> [(Float , Float)]
boxCoorPre m = boxCoorPre' m (coorMorph m)

boxCoorPre' :: Morph -> [(Float , Float)] -> [(Float , Float)]
boxCoorPre' (Start _) _ = []
boxCoorPre' (Op m _ _) [] = (0 , 0) : boxCoorPre' m []
boxCoorPre' (Op m _ (Comp _ (Start _))) (_ : l) = boxCoorPre' m l
boxCoorPre' (Op m i (Comp w (Op n _ _))) (p : l) = p : boxCoorPre' (Op m i (Comp w n)) (p : l)
boxCoorPre' (Op m _ _) (p : l) = p : boxCoorPre' m l


boxCoorPost :: Morph -> [(Float , Float)]
boxCoorPost m = boxCoorPost' m (coorMorph m)

boxCoorPost' :: Morph -> [(Float , Float)] -> [(Float , Float)]
boxCoorPost' (Start _) _ = []
boxCoorPost' (Op m _ _) [] = (0 , 0) : boxCoorPost' m []
boxCoorPost' (Op m i (Comp (RS _ n _ _) _)) l = boxCoorPost' (Op m i (Comp (RI n) n)) l
boxCoorPost' (Op m _ (Comp (RI (Start _)) _)) (_ : l) = boxCoorPost' m l
boxCoorPost' (Op m i (Comp (RI (Op n _ _)) k)) (p : l) = p : boxCoorPost' (Op m i (Comp (RI n) k)) (p : l)
boxCoorPost' (Op m _ _) (p : l) = p : boxCoorPost' m l


-- UNUSED ?


-- sort out the morph
coorsortMorph :: Morph -> [(Float, Float , Bool)] -> (Morph , [(Float, Float , Bool)])
coorsortMorph m coor = let n = knayMorph m in (n , coormatchMorph m (knayMorph m) coor)
--    let (n , perm) = knayMorphRem m in
--    let door = applyPermCoor perm coor in 
--        (n , door)




permmatchMorph :: Morph -> Morph -> Perm
permmatchMorph m n = 
    let (_ , perm) = knayMorphRem m in 
    let (_ , pern) = knayMorphRem n in 
        compPerm perm (reversePerm pern)

coormatchMorph :: Morph -> Morph -> [(Float, Float , Bool)] -> [(Float, Float , Bool)]
coormatchMorph m n coor = 
    let perm = permmatchMorph m n in
        applyPermCoor perm coor


