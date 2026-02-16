{-# LANGUAGE InstanceSigs #-}
module Morph where


-- Extended libraries


-- =============================================
-- The Morphism Datatype as combinatorial object
-- =============================================

-- Below determines how much space is allocated to wires as a ration. E.g. now it is  1:1  ratio  wires:boxes
wirerat :: Float
wirerat = 1

-- ===========================================================================
-- Utility functions for convenience (may be replaced basic library functions)
-- ===========================================================================


tryAny :: (a -> Maybe b) -> [a] -> Maybe b
tryAny _ [] = Nothing
tryAny f (a : l) = case f a of
    Just b      ->  Just b
    Nothing     ->  tryAny f l


inSet :: Ord a => a -> [a] -> Bool
inSet _ [] = False
inSet x (y : l)
    |   x > y       =   inSet x l
    |   otherwise   =   x == y

subSet :: Ord a => [a] -> [a] -> Bool
subSet [] _ = True
subSet _ [] = False
subSet (x : l) (y : r)
    |   x < y       =   False
    |   x == y      =   subSet l r
    |   otherwise   =   subSet (x : l) r

addSet :: Ord a => a -> [a] -> [a]
addSet a [] = [a]
addSet a (b : l)
    |   a < b       =   a : b : l
    |   a == b      =   b : l
    |   otherwise   =   b : addSet a l

sortSet :: Ord a => [a] -> [a]
sortSet = foldr addSet []

joinSet :: Ord a => [a] -> [a] -> [a]
joinSet l [] = l
joinSet [] r = r
joinSet (a : l) (b : r)
    |   a < b       =   a : joinSet l (b : r)
    |   a == b      =   a : joinSet l r
    |   otherwise   =   b : joinSet (a : l) r

intSet :: Ord a => [a] -> [a] -> Bool
intSet _ [] = False
intSet [] _ = False
intSet (a : r) (b : l)
    |   a < b       =   intSet r (b : l)
    |   a == b      =   True
    |   otherwise   =   intSet (a : r) l

delSet :: Ord a => a -> [a] -> [a]
delSet _ [] = []
delSet a (b : l)
    |   a < b       =   b : l
    |   a == b      =   l
    |   otherwise   =   b : delSet a l

lastList :: a -> [a] -> a
lastList m [] = m
lastList _ (n : l) = lastList n l

-- Lookup Option from signature list
lookupSig :: Char -> [Sig] -> Maybe Sig
lookupSig _ [] = Nothing
lookupSig c ((Sig d s i o) : sig)
    |   c == d      =   Just (Sig d s i o)
    |   otherwise   =   lookupSig c sig


-- Fractions datat type: as alternative to floating numbers
type Frac = (Int , Int)

frac2Float :: Frac -> Float
frac2Float (a , b) = fromIntegral a / fromIntegral b


-- ====================================================
-- Main datatypes for formulating the monoidal category
-- ====================================================

-- The object datatype: Objects of the category are given by "number of strings"
type Object = Int

-- Drawing styles for operations, simply with names now. May replace by datatype later
type Style = String

-- The signature datatype: describing the signature of a basic atomic operation
-- Char: the key binding character for type setting and storing. Functions as the name (yes, each operation should be bound to a different character)
-- Style: Drawing style for visualisation
-- Objects: Input and output type
data Sig =
    Sig Char Style Object Object
    deriving (Eq , Ord , Show)

-- Operationst data type: Either atomic, or composite
-- Composite operation come with a rewrite state REW: that is a rewrite into another composite
-- and a history Morph: the composite morphism it was before rewriting
data Oper =
    Base Sig
    |   Comp Rew Morph
    deriving (Eq , Ord)

-- Morphisms data type: Either an identity morphism used as starting point, or another morphism composed with an operation
-- Op m i o: m is the preceeding morphism, o the new operation, and i the (vertical) position of the new operation, that is the number of wires it skips
data Morph =
    Start Object
    |   Op Morph Int Oper
    deriving (Eq)

-- Rewrite state 
data Rew =
    RI Morph            -- Same as start, categorical equality
    |   RS MR Morph     -- Rewrite with rule into
    deriving (Eq , Ord)

-- Rewrite rule type: the new state is equal/larger/smaller than the former
data MR =
    MEqual
    |   MLarger
    |   MSmaller
    deriving (Eq , Show , Ord)

-- Utility functions for rewrites
firstRew :: [Rew] -> Morph 
firstRew [] = Start 0 
firstRew (RI m : _) = m
firstRew (RS _ m : _) = m

tailList :: [a] -> [a]
tailList [] = []
tailList (_ : l) = l

reverseRew :: Rew -> Rew
reverseRew (RI m)   = RI m
reverseRew (RS x m) = RS (reverseMR x) m

reverseHis :: [Rew] -> [Rew]
reverseHis (RI m : RS x n : l) = RS (reverseMR x) m : reverseHis (RI n : l)
reverseHis l = l

reverseSih :: [Rew] -> [Rew]
reverseSih his = reverse (reverseHis (reverse his))

rewMorph :: Rew -> Morph
rewMorph (RI m) = m
rewMorph (RS _ m) = m

rewSub :: Rew -> Morph -> Rew
rewSub (RI _) m = RI m
rewSub (RS x _) m = RS x m

-- The relation/rewrite rule datatype: Two morphisms with an associated relation type
type Relat = (MR , Morph , Morph)

-- remove trivial relations
remRelat :: [Relat] -> [Relat]
remRelat [] = []
remRelat ((e , m , n) : l) 
    |   m == n      =   remRelat l
    |   otherwise   =   (e , m , n) : remRelat l

-- ============================
-- Morphism auxiliary functions
-- ============================

-- safe mode: a rewrite is not progress
safeMorph :: Morph -> Bool
safeMorph (Start _) = True 
safeMorph (Op m _ (Base _)) = safeMorph m 
safeMorph (Op m _ (Comp (RI _) _)) = safeMorph m
safeMorph (Op _ _ (Comp (RS _ _) _)) = False

-- apply mode: we can apply rewrite to morphis
countMorph :: Morph -> Int
countMorph (Start _) = 0
countMorph (Op m _ (Base _)) = countMorph m 
countMorph (Op m _ (Comp _ _)) = 1 + countMorph m

relatWrap :: MR -> Morph -> Morph -> Relat 
relatWrap x m n = (x , m , n)

reverseMR :: MR -> MR
reverseMR MEqual = MEqual
reverseMR MLarger = MSmaller
reverseMR MSmaller = MLarger

relatMR :: Relat -> MR
relatMR (m , _ , _) = m

startRelat :: Relat -> Morph
startRelat (_ , m , _) = m

goalRelat :: Relat -> Morph
goalRelat (_ , _ , n) = n

orderMorph :: Morph -> Morph -> Bool
orderMorph (Start o)        (Start o')          =   o <= o'
orderMorph (Start _)        _                   =   True
orderMorph _                (Start _)           =   False
orderMorph (Op m i o)       (Op m' i' o')
    |   i < i'      =   True
    |   i > i'      =   False
    |   o < o'      =   True
    |   o > o'      =   False
    |   otherwise   =   orderMorph m m'

instance Ord Morph where
    (<=) :: Morph -> Morph -> Bool
    m <= m'
        |   bulkMorph m == bulkMorph m' =   orderMorph m m'
        |   otherwise                       =   bulkMorph m <= bulkMorph m'

-- ==================
-- Printing morphisms
-- ==================

instance Show Oper where
    show :: Oper -> String
    show (Base (Sig c t i o))   =   c : t ++ ":" ++ show i ++ "->" ++ show o
    show (Comp m _)             =   show (rewMorph m)

showm :: Morph -> String
showm (Start _) = ""
showm (Op (Start _) i o) = "(" ++ show i ++ "|" ++ show o ++ ")"
showm (Op m i o) = showm m ++ ";(" ++ show i ++ "|" ++ show o ++ ")"


instance Show Morph where
    show :: Morph -> String
    show m = let (i , o) = typeMorph m in "{" ++ showm m ++ "}:" ++ show i ++ "->" ++ show o

layerPrintOper :: Int -> Int -> Oper -> [String]
--layerPrintOper i j (Base [] a b) = [show i ++ " | :" ++ show a ++ "->" ++ show b ++ " | " ++ show j]
layerPrintOper i j (Base (Sig c _ a b)) = [show i ++ " | " ++ c : ":" ++ show a ++ "->" ++ show b ++ " | " ++ show j]
layerPrintOper i j (Comp m _)           = let (im , om) = typeMorph (rewMorph m) in
    (show i ++ " | [-]:" ++ show im ++ "->" ++ show om ++ " | " ++ show j) : fmap ("    " ++ ) (layerPrintMorph (rewMorph m))

layerPrintMorph :: Morph -> [String]
layerPrintMorph (Start _) = []
layerPrintMorph (Op m i p) =
    let (_ , om) = typeMorph m in
    let (ip , _) = typeOper p in
    layerPrintMorph m ++ layerPrintOper i (om-ip-i) p

layerPrintMorph' :: Morph -> [String]
layerPrintMorph' m = let (im , om) = typeMorph m in ("[-]:" ++ show im ++ "->" ++ show om) : layerPrintMorph m

lineString :: [String] -> String
lineString [] = ""
lineString [a] = a
lineString (a : l) = a ++ "\n" ++ lineString l

-- =========================================
-- FANCY PRINT: Multi line print in terminal
-- =========================================


takeL :: Int -> Int -> [a] -> ([a] , [a])
takeL _ _ [] = ([] , [])
takeL i j (c : l)
    |   i > 0       =   let (x , y) = takeL (i-1) j l in (x , c : y)
    |   j > 0       =   let (x , y) = takeL i (j-1) l in (c : x , y)
    |   otherwise   =   ([] , c : l)

repL :: Int -> Int -> [a] -> [a] -> ([a] , [a])
repL _ _ [] r = ([] , r)
repL i j (c : l) r
    |   i > 0       =   let (x , y) = repL (i-1) j l r in (x , c : y)
    |   j > 0       =   let (x , y) = repL i (j-1) l r in (c : x , y)
    |   otherwise   =   ([] , r ++ c : l)

-- Generating fresh variable
freshL :: [Int] -> Int -> [Int]
freshL l = freshL' (maximum l + 1)

freshL' :: Int -> Int -> [Int]
freshL' i j
    |   j <= 0      =   []
    |   otherwise   =   i : freshL' (i+1) (j-1)

-- Copying the i-th variable in context
copyV :: Int -> [Int] -> [Int]
copyV _ [] = []
copyV i (a : v)
    |   i <= 0      =   a : a : v
    |   otherwise   =   a : copyV (i-1) v

-- Discarding the i-th variable in context
discardV :: Int -> [Int] -> [Int]
discardV _ [] = []
discardV i (a : v)
    |   i <= 0      =   v
    |   otherwise   =   a : discardV (i-1) v

-- Swapping i-th and (i+1)-th variable in context
swapV :: Int -> [Int] -> [Int]
swapV i (a : b : v)
    |   i <= 0      =   b : a : v
    |   otherwise   =   a : swapV (i-1) (b : v)
swapV _ l = l

-- Finding i-th variable in context
takeV :: Int -> [Int] -> Int
takeV _ [] = -1
takeV i (a : l)
    |   i <= 0      =   a
    |   otherwise   =   takeV (i-1) l

-- Initiating multiline print
printMorphI :: Morph -> String
printMorphI m = let (a , _) = typeMorph m in
    "M" ++ show [0 .. a-1] ++ ":"
    ++ printMorphE "  " [0 .. a-1] a m

-- Printing multiple lines using list of variable names 
printMorph :: String -> [Int] -> Int -> Morph -> (String , [Int] , Int)
printMorph _ v fs (Start _) = ("" , v , fs)
printMorph s v fs (Op m i (Base (Sig 'x' "1" 2 2))) =
    let (q , w , fs2) = printMorph s v fs m in
        (q , swapV i w , fs2)
printMorph s v fs (Op m i (Base (Sig 'c' "2" 1 2))) =
    let (q , w , fs2) = printMorph s v fs m in
        (q , copyV i w , fs2)
printMorph s v fs (Op m i (Base (Sig 'd' "2" 1 0))) =
    let (q , w , fs2) = printMorph s v fs m in
        (q , discardV i w , fs2)
printMorph s v fs (Op m i (Base (Sig 'l' "" 1 1))) =
    let (q , w , fs2) = printMorph s v fs m in
        (q ++ "\n" ++ s ++ "l(" ++ show (takeV i w) ++ ")" , w , fs2)
printMorph s v fs (Op m i (Base (Sig c _ a b))) =
    let (q , w , fs2) = printMorph s v fs m in
    let f = [fs2 .. (fs2+b-1)] in
    let (x , y) = repL i a w f in
        (q ++ "\n" ++ s ++ show f ++ " := " ++ c : show x , y , fs2+b)
printMorph s v fs (Op m i (Comp n _)) =
    let (ms , mv , fs2) = printMorph s v fs m in
    let (a , b) = typeMorph (rewMorph n) in
    let (x , _) = takeL i a mv in
    let (ns , nv , fs3) = printMorph ("  " ++ s) x fs2 (rewMorph n) in
    let f = [fs3 .. (fs3+b-1)] in
    let (_ , y) = repL i a mv f in
        (ms ++ "\n" ++ s ++ show f ++ " <-" ++ ns ++ "\n" ++ s ++ "  return " ++ show nv , y , fs3+b)
--printMorph _ _ _ _ = ("" , [] , 0)

printMorphE :: String -> [Int] -> Int -> Morph -> String
printMorphE s v fs m = let (q , w , _) = printMorph s v fs m in
    q ++ "\n" ++ s ++ "return " ++ show w


-- ======================================
-- Basic utility on the Morphism datatype
-- ======================================

isOp :: Morph -> Maybe (Int , Oper , Morph)
isOp (Start _) = Nothing
isOp (Op m i o) = Just (i , o , m)

typeOper :: Oper -> (Object , Object)
typeOper (Base (Sig _ _ i o)) = (i , o)
typeOper (Comp m _) = typeMorph (rewMorph m)

typeMorph :: Morph -> (Object , Object)
typeMorph (Start o) = (o , o)
typeMorph (Op m i o)  =
    let (mi , mo) = typeMorph m in
    let (bi , bo) = typeOper o in
    if (i+bi) <= mo then
        (mi , mo-bi+bo)
    else
        (-10 , -100)

lengthMorph :: Morph -> Int
lengthMorph (Start _) = 1
lengthMorph (Op m _ _) = 1 + lengthMorph m

bulkMorph :: Morph -> Int
bulkMorph (Start _) = 0
bulkMorph (Op m _ o) = let (x , y) = typeOper o in 1 + x + y + bulkMorph m

reduceMorph :: Morph -> Morph -> Bool
reduceMorph m n = bulkMorph n < bulkMorph m

-- checks if the next two Option are independent
squeezeMorph :: Morph -> Bool
squeezeMorph (Op (Op _ j p) i o ) =
    let (ii , _) = typeOper o in
    let (_ , jo) = typeOper p in
        ((j + jo) <= i || (i + ii) <= j) && (i /= j || ii /= 0 || jo /= 0)
squeezeMorph _ = False

-- size with squeezes
sizeMorph :: Morph -> Float
sizeMorph (Start _) = wirerat
sizeMorph (Op m i o) = if squeezeMorph (Op m i o) then sizeOper o + sizeMorph m else wirerat + sizeOper o + sizeMorph m

-- size without sequeezes
sizeMorph' :: Morph -> Float
sizeMorph' (Start _) = wirerat
sizeMorph' (Op m _ o) = wirerat + sizeOper o + sizeMorph' m

sizeOper :: Oper -> Float
sizeOper (Base {}) = 1
sizeOper (Comp _ _) = 2 + wirerat

-- Basic coordinates of nodes in morphism
coorMorph :: Morph -> [(Float , Float)]
coorMorph m = coorMorph' wirerat (sizeMorph m) m

coorMorph' :: Float -> Float -> Morph -> [(Float , Float)]
coorMorph' _ _ (Start _) = []
coorMorph' posx width (Op m i o) =
    let c = sizeOper o in
    let squ = squeezeMorph (Op m i o) in
    let nexx = if squ then posx+c else posx+c+wirerat in
    let coorm = coorMorph' nexx width m in
    let (_ , mo) = typeMorph m in
    let (bi , bo) = typeOper o in
    let x = 1 - ((posx + c/2) / width) in
    let y = frac2Float (2 + 4*i + bi + bo , 4 - 2*bi + 2*bo + 4*mo) in
        ((x , y) : coorm)


-- ===================================
-- Theoretical Options on Morphisms
-- ===================================

-- Weakening context: add wires below and above
weakenMorph :: Int -> Int -> Morph -> Morph
weakenMorph i j (Start k) = Start (i+k+j)
weakenMorph i j (Op m k o) = Op (weakenMorph i j m) (i+k) o

-- Composition of morphisms, untyped and unsafe
compMorph :: Morph -> Morph -> Morph
compMorph (Start _) n = n
compMorph (Op m i o) n = Op (compMorph m n) i o

-- More general Merging of morphisms
mergeMorph  :: (Int , Morph) -> (Int , Morph) -> (Int , Morph)
mergeMorph (i , m) (j , n) =
    let (mi , _) = typeMorph m in
    let (_ , no) = typeMorph n in
    let n' = weakenMorph (max 0 (j-i)) (max 0 (i + mi - j - no)) n in
    let m' = weakenMorph (max 0 (i-j)) (max 0 (j + no - i - mi)) m in
        (min i j , compMorph m' n')

-- A single Option as a morphism
operMorph :: Oper -> Morph
operMorph (Base (Sig f s i o)) = Op (Start i) 0 (Base (Sig f s i o))
operMorph (Comp m _) = rewMorph m

mergeOper  :: (Int , Oper) -> (Int , Oper) -> (Int , Oper)
mergeOper (i , o) (j , p) =
    let (k , q) = mergeMorph (i , operMorph o) (j , operMorph p) in
    let m = knayMorph (insertSort q) in (k , Comp (RI m) m)

checkMerge :: Morph -> Maybe Morph
checkMerge (Op _ _ (Comp (RS _ _) _)) = Nothing
checkMerge (Op (Op _ _ (Comp (RS _ _) _)) _ _) = Nothing
checkMerge (Op (Op m j p) i o) = let (k , q) = mergeOper (i , o) (j , p) in Just (Op m k q)
checkMerge _ = Nothing

-- Rewrite: 
rewriteNode :: (Rew -> Morph -> Rew) -> (Float , Float) -> Float -> Morph -> [(Float , Float , Bool)] -> Morph
rewriteNode _ _ _ (Start i) _ = Start i
rewriteNode _ _ _ (Op i o m) [] = Op i o m
rewriteNode f (mx , my) bs (Op m i o) ((x , y , _) : r)
    |   abs (mx-x) <= 2*bs && abs (my-y) <= 2*bs   =  case o of
            Comp n nh           ->  Op m i (Comp (f n nh) nh)
            Base (Sig g s a b)  ->  let n = Op (Start a) 0 (Base (Sig g s a b)) in
                                    let p = f (RI n) n in Op m i (Comp p n)
    |   otherwise   =   let n = rewriteNode f (mx , my) bs m r in Op n i o

morphOps :: Morph -> [Sig]
morphOps (Start _) = []
morphOps (Op m _ (Base s)) = addSet s (morphOps m)
morphOps (Op m _ (Comp n _)) = joinSet (morphOps (rewMorph n)) (morphOps m)

-- Checks if there are boxes in the morphism
flatMorph :: Morph -> Bool
flatMorph (Start _) = True
flatMorph (Op m _ (Base {})) = flatMorph m
flatMorph (Op _ _ (Comp _ _)) = False

eqMorph :: Morph -> Morph -> Bool
eqMorph m n = insertSort m == insertSort n

-- 
sapMorph :: Morph -> [a] -> [(Morph , [a])]
sapMorph (Op (Op m j q) i o) (p : p' : r) =
    let (oi , oo) = typeOper o in
    let (qi , qo) = typeOper q in
    if oi == 0 && qo == 0 && i == j then
        [(Op (Op m (i-qo+qi) o) j q , p' : p : r) ,
        (Op (Op m i o) (j-oi+oo) q , p' : p : r)]
    else
        if (j + qo) <= i then
            [(Op (Op m (i-qo+qi) o) j q , p' : p : r)]
        else
            ([(Op (Op m i o) (j-oi+oo) q , p' : p : r) | (i + oi) <= j])
sapMorph _ _ = []

allMorph :: (Morph , [a]) -> [(Morph , [a])]
allMorph (Op m i o , p : l) = sapMorph (Op m i o) (p : l) ++ [(Op n i o , p : r) | (n , r) <- allMorph (m , l)]
allMorph _ = []

addMorph :: (Morph , [a]) -> [(Morph , [a])] -> Maybe [(Morph , [a])]
addMorph (m , l) [] = Just [(m , l)]
addMorph (m , l) ((n , r) : v)
    |   m < n       =   Just ((m , l) : (n , r) : v)
    |   m == n      =   Nothing
    |   otherwise   =   fmap ((n , r) :) (addMorph (m , l) v)

chucker :: Int -> [(Morph , [a])] -> [(Morph , [a])] -> [(Morph , [a])]
chucker _ box [] = box
chucker i box (new : rest)
    |   i > 0       = case addMorph new box of
        Just box'   ->  chucker (i-1) box' (rest ++ allMorph new)
        Nothing     ->  chucker i box rest
    |   otherwise   =   box

trucker :: (Morph , [a]) -> [(Morph , [a])]
trucker m = chucker 100 [] [m]

-- ==========================
-- Automatic matcher of rules
-- ==========================

-- exact match of submorphism
exactSubMorph :: Int -> Morph -> Morph -> Bool
exactSubMorph _ _ (Start _)                      =   True
exactSubMorph _ (Start _) _                      =   False
exactSubMorph j (Op m k o) (Op m' k' o')   =   ((j + k') == k) && o == o' && exactSubMorph j m m'


matchSubMorph :: Int -> Morph -> Morph -> Maybe (Int , Int)
matchSubMorph i _               (Start _)           =    Just (i , 0)
matchSubMorph _ (Start _)       _                   =    Nothing
matchSubMorph i (Op m k o)   (Op m' k' o')
    |   o == o' && k >= k'  =   if exactSubMorph (k-k') m m' then Just (i , k-k') else matchSubMorph (i+1) m (Op m' k' o')
    |   otherwise           =   matchSubMorph (i+1) m (Op m' k' o')

replaceSubMorph :: Int -> Int -> Int -> Morph -> Morph -> Morph
replaceSubMorph _ _ _ (Start a) (Start _) = Start a
replaceSubMorph i j k (Op m a o) (Start b)
    |   i > 0       =   Op (replaceSubMorph (i-1) j k m (Start b)) a o
    |   k > 0       =   replaceSubMorph i j (k-1) m (Start b)
    |   otherwise   =   Op m a o
replaceSubMorph _ j _ (Start a) m = let (x , _) = typeMorph m in weakenMorph j (a-x-j) m
replaceSubMorph i j k (Op m a o) (Op n b q)
    |   i > 0       =   Op (replaceSubMorph (i-1) j k m (Op n b q)) a o
    |   k > 0       =   replaceSubMorph i j (k-1) m (Op n b q)
    |   otherwise   =   Op (replaceSubMorph 0 j 0 (Op m a o) n) (b+j) q

-- match and replace
marSubMorph :: Morph -> Morph -> Morph -> Maybe Morph
marSubMorph m s n = matchSubMorph 0 m s >>= \(i , j) -> Just (replaceSubMorph i j (lengthMorph s - 1) m n)


-- find reductions
redrule :: (a -> a -> Bool) -> [[a]] -> [(a , a)]
redrule _ [] = []
redrule f ([] : v) = redrule f v
redrule f ((a : l) : v) = redrule' f a l ++ redrule f v

redrule' :: (a -> a -> Bool) -> a -> [a] -> [(a , a)]
redrule' _ _ [] = []
redrule' f x (y : l)
    |   f y x       =   (y , x) : redrule' f x l
    |   otherwise   =   redrule' f x l


anyred :: Morph -> [a] ->  [[Morph]] -> Maybe Morph
anyred m l eq = anyred2 (trucker (m , l)) (redrule reduceMorph eq)

anyred2 :: [(Morph , [a])] -> [(Morph , Morph)] -> Maybe Morph
anyred2 a b = tryAny (\(x , y , z) -> marSubMorph x y z) [(m , s , n) | (m , _) <- a , (s , n) <- b]


anyredFull :: Float -> Morph -> [(Float , Float , Bool)] -> [[Morph]] -> Maybe (Morph , [(Float , Float , Bool)])
anyredFull s m loc eq = anyred m loc eq >>= \n -> Just (n , [(s * a , s * b , False) | (a , b) <- coorMorph n])

-- ===========================
-- Sorting nodes in a morphism
-- ===========================
cleanMorph :: Morph -> Morph 
cleanMorph m = knayMorph (insertSort m)

insertSort :: Morph -> Morph
insertSort (Start i) = Start i
insertSort (Op m i o) = insertSort' (Op (insertSort m) i o)

insertSort' :: Morph -> Morph
insertSort' (Op (Op n j p) i o) = let (io , oo) = typeOper o in
    if (i + io) <= j then Op (insertSort' (Op n i o)) (j - io + oo) p else Op (Op n j p) i o
insertSort' m = m

sortRelat :: Relat -> Relat
sortRelat (x , m , n) = (x , insertSort m , insertSort n)

-- =======================================================
-- Reordering operation to be better spread out vertically
-- =======================================================


-- Alternative Data Structure for Morphisms as input type and lists of operations
type LMorph = (Object , [(Object , Oper)])

-- Transforming Morph into LMorph
listMorph :: Morph -> LMorph
listMorph (Start i) = (i , [])
listMorph (Op m i o) = let (j , l) = listMorph m in (j , l ++ [(i , o)])

-- Building Morph from Lmorph (should be each others inverse on correct morphisms)
buildMorph :: LMorph -> Morph
buildMorph (i , l) = buildMorph' (Start i) l

buildMorph' :: Morph -> [(Object , Oper)] -> Morph 
buildMorph' m [] = m
buildMorph' m ((i , o) : l) = buildMorph' (Op m i o) l

-- Finding the next operation connected to a particular wire. Checks if that operation can be put in front
layerKnay :: Int -> Int -> [(Object , Oper)] -> Maybe (Oper , [(Object , Oper)])
layerKnay _ _ [] = Nothing
layerKnay h i ((j , o) : l) 
    |   i == j && fst (typeOper o) > 0          
                        =   Just (o , l)
    |   i >= h          =   Nothing 
    |   i < j           =   let (io , oo) = typeOper o in 
                            layerKnay (h-io+oo) i l >>= \(q , r) -> 
                            let (iq , oq) = typeOper q in 
                            if (i + iq) > j then Nothing else Just (q , (j-iq+oq , o) : r)
    |   otherwise       =   let (io , oo) = typeOper o in 
                            if i < (j + io) then Nothing else 
                            layerKnay (h-io+oo) (i-io+oo) l >>= \(q , r) -> 
                            Just (q , (j , o) : r)

-- Reorders operations 
layersKnay :: Int -> Int -> Bool -> [(Object , Oper)] -> [(Object , Oper)]
layersKnay _ _ _ [] = []
layersKnay h i k ((j , o) : l) = 
    case layerKnay h i ((j , o) : l) of 
        Just (q , r)    ->  let (iq , oq) = typeOper q in 
                            (i , q) : layersKnay (h-iq+oq) (i+oq) True r
        Nothing         ->  let (io , oo) = typeOper o in 
                            if i >= h then 
                                if k then layersKnay h 0 False ((j , o) : l) 
                                else (j , o) : layersKnay (h-io+oo) (i+oo) True l
                            else layersKnay h (i+1) k ((j , o) : l)

knay :: LMorph -> LMorph 
knay (i , l) = (i , layersKnay i 0 False l)

knayMorph :: Morph -> Morph 
knayMorph m = buildMorph (knay (listMorph m))


