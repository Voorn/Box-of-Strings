{-# LANGUAGE InstanceSigs #-}
module Morph where

import Matcher

-- S

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

uptoBar :: String -> String
uptoBar [] = []
uptoBar ('|' : _) = []
uptoBar (c : l) = c : uptoBar l


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

lookList :: Int -> a -> [a] -> a
lookList _ a [] = a
lookList i _ (b : l)
    |   i <= 0      =   b
    |   otherwise   =   lookList (i-1) b l

lookupList :: Int -> [a] -> Maybe a
lookupList _ [] = Nothing
lookupList i (a : l)
    |   i <= 0      =   Just a
    |   otherwise   =   lookupList (i-1) l

updateList :: Int -> a -> [a] -> [a]
updateList _ _ [] = []
updateList i a (b : l)
    |   i == 0      =   a : l
    |   otherwise   =   b : updateList (i-1) a l


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
type Style = (Maybe Exp , String)

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
    |   Func String Morph
    deriving (Eq , Ord)

-- Morphisms data type: Either an identity morphism used as starting point, or another morphism composed with an operation
-- Op m i o: m is the preceeding morphism, o the new operation, and i the (vertical) position of the new operation, that is the number of wires it skips
data Morph =
    Start Object
    |   Op Morph Int Oper
    deriving (Eq)

-- Rewrite state 
data Rew =
    RI Morph                    -- Same as start, categorical equality
    |   RS MR Morph String Why  -- Rewrite with rule into
    deriving (Eq , Ord , Show)

isAxiom' :: Rew -> Bool
isAxiom' (RI _) = True
isAxiom' (RS _ _ _ w) = isAxiom w

-- Rewrite rule type: the new state is equal/larger/smaller than the former
data MR =
    MEqual
    |   MLarger
    |   MSmaller
    deriving (Eq , Show , Ord)

rewText :: Rew -> String
rewText (RS _ _ s _) = s
rewText _ = ""

nameSig :: Sig -> Char
nameSig (Sig c _ _ _) = c

-- Utility functions for rewrites
firstRew :: [Rew] -> Morph
firstRew [] = Start 0
firstRew (RI m : _) = m
firstRew (RS _ m _ _ : _) = m

tailList :: [a] -> [a]
tailList [] = []
tailList (_ : l) = l

reverseRew :: Rew -> Rew
reverseRew (RI m)   = RI m
reverseRew (RS x m s w) = RS (reverseMR x) m s w

reverseHis :: [Rew] -> [Rew]
reverseHis (RI m : RS x n s w : l) = RS (reverseMR x) m s w : reverseHis (RI n : l)
reverseHis l = l

reverseSih :: [Rew] -> [Rew]
reverseSih his = reverse (reverseHis (reverse his))

rewMorph :: Rew -> Morph
rewMorph (RI m) = m
rewMorph (RS _ m _ _) = m

rewSub :: Rew -> Morph -> Rew
rewSub (RI _) m = RI m
rewSub (RS x _ s w) m = RS x m s w

data Why =
    Axiom
    |   Lemma
    |   Show
--    |   Schema Why
    deriving (Eq , Ord , Show)

isAxiom :: Why -> Bool
isAxiom Axiom = True
isAxiom _ = False

-- The relation/rewrite rule datatype: Two morphisms with an associated relation type
type Relat = (MR , Morph , Morph , String , Why)

baseRelat :: Relat
baseRelat = (MEqual , Start 0 , Start 0 , "" , Show)

-- remove trivial relations
remRelat :: [Relat] -> [Relat]
remRelat [] = []
remRelat ((e , m , n , t , w) : l)
    |   m == n      =   remRelat l
    |   otherwise   =   (e , m , n , t , w) : remRelat l

-- ============================
-- Morphism auxiliary functions
-- ============================

-- safe mode: a rewrite is not progress
safeMorph :: Morph -> Bool
safeMorph (Start _) = True
safeMorph (Op m _ (Base _)) = safeMorph m
safeMorph (Op m _ (Comp (RI _) _)) = safeMorph m
safeMorph (Op _ _ (Comp (RS {}) _)) = False
safeMorph (Op m _ (Func _ n)) = safeMorph m && safeMorph n

-- apply mode: we can apply rewrite to morphis
countMorph :: Morph -> Int
countMorph (Start _) = 0
countMorph (Op m _ (Base _)) = countMorph m
countMorph (Op m _ (Comp _ _)) = 1 + countMorph m
countMorph (Op m _ (Func _ n)) = countMorph m + countMorph n

relatWrap :: MR -> Morph -> Morph -> String -> Why -> Relat
relatWrap x m n t w = (x , m , n , t , w)

reverseMR :: MR -> MR
reverseMR MEqual = MEqual
reverseMR MLarger = MSmaller
reverseMR MSmaller = MLarger

joinMRunsafe :: MR -> MR -> MR
joinMRunsafe MEqual y   = y
joinMRunsafe x MEqual   = x
joinMRunsafe x _        = x

relatMR :: Relat -> MR
relatMR (m , _ , _ , _ , _) = m

startRelat :: Relat -> Morph
startRelat (_ , m , _ , _ , _) = m

goalRelat :: Relat -> Morph
goalRelat (_ , _ , n , _ , _) = n

nameRelat :: Relat -> String
nameRelat (_ , _ , _ , t , _) = t

whyRelat :: Relat -> Why
whyRelat (_ , _ , _ , _ , w) = w

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
        |   otherwise                   =   bulkMorph m <= bulkMorph m'

-- ==================
-- Printing morphisms
-- ==================

instance Show Oper where
    show :: Oper -> String
    show (Base (Sig c (Nothing , t) i o))   =   c : t ++ ":" ++ show i ++ "->" ++ show o
    show (Base (Sig c (Just e , t) i o))   =   c : '(' : show e ++ ')' : t ++ ":" ++ show i ++ "->" ++ show o
    show (Comp m _)             =   show (rewMorph m)
    show (Func c m)             =   c ++ "[" ++ show m ++ "]"

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
layerPrintOper i j (Func c m)           = let (im , om) = typeMorph m in
    (show i ++ " | " ++ c ++ "[-]:" ++ show im ++ "->" ++ show om ++ " | " ++ show j) : fmap ("    " ++ ) (layerPrintMorph m)


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

varname :: Int -> Char
varname i = lookList i '-' "abcdefghijklmnopqrstuvwxyz"

varlist :: [Int] -> String
varlist l = '(' : varlist' l

varlist' :: [Int] -> String
varlist' [] = ")"
varlist' [i] = varname i : ")"
varlist' (i : l) = varname i : ',' : varlist' l

-- Initiating multiline print
printMorphI :: Morph -> String
printMorphI m = let (a , _) = typeMorph m in
    "F" ++ varlist [0 .. a-1] ++ ":"
    ++ printMorphE " " [0 .. a-1] a m

-- Printing multiple lines using list of variable names 
printMorph :: String -> [Int] -> Int -> Morph -> (String , [Int] , Int)
printMorph _ v fs (Start _) = ("" , v , fs)
printMorph s v fs (Op m i (Base (Sig 'x' (Nothing ,"1") 2 2))) =
    let (q , w , fs2) = printMorph s v fs m in
        (q , swapV i w , fs2)
printMorph s v fs (Op m i (Base (Sig 'c' (Nothing , "2") 1 2))) =
    let (q , w , fs2) = printMorph s v fs m in
        (q , copyV i w , fs2)
printMorph s v fs (Op m i (Base (Sig 'd' (Nothing , "2") 1 0))) =
    let (q , w , fs2) = printMorph s v fs m in
        (q , discardV i w , fs2)
printMorph s v fs (Op m i (Base (Sig 'l' (Nothing , "leak") 1 1))) =
    let (q , w , fs2) = printMorph s v fs m in
        (q ++ "\n" ++ s ++ "leak" ++ varlist [takeV i w] , w , fs2)
printMorph s v fs (Op m i (Base (Sig 'q' (Nothing , "leak") 1 0))) =
    let (q , w , fs2) = printMorph s v fs m in
        (q ++ "\n" ++ s ++ "leak" ++ varlist [takeV i w] , discardV i w , fs2)
printMorph s v fs (Op m i (Base (Sig 'r' _ a b))) =
    let (q , w , fs2) = printMorph s v fs m in
    let f = [fs2 .. (fs2+b-1)] in
    let (x , y) = repL i a w f in
        (q ++ "\n" ++ s ++ varlist f ++ " <- xor" ++ varlist x , y , fs2+b)
printMorph s v fs (Op m i (Base (Sig '?' _ a b))) =
    let (q , w , fs2) = printMorph s v fs m in
    let f = [fs2 .. (fs2+b-1)] in
    let (x , y) = repL i a w f in
        (q ++ "\n" ++ s ++ varlist f ++ " <- k" ++ varlist x , y , fs2+b)
printMorph s v fs (Op m i (Base (Sig c _ a b))) =
    let (q , w , fs2) = printMorph s v fs m in
    let f = [fs2 .. (fs2+b-1)] in
    let (x , y) = repL i a w f in
        (q ++ "\n" ++ s ++ varlist f ++ " <- " ++ c : varlist x , y , fs2+b)
printMorph s v fs (Op m i (Comp n _)) =
    let (ms , mv , fs2) = printMorph s v fs m in
    let (a , b) = typeMorph (rewMorph n) in
    let (x , _) = takeL i a mv in
    let (ns , nv , fs3) = printMorph ("  " ++ s) x fs2 (rewMorph n) in
    let f = [fs3 .. (fs3+b-1)] in
    let (_ , y) = repL i a mv f in
        (ms ++ "\n" ++ s ++ varlist f ++ " <-" ++ ns ++ "\n" ++ s ++ "  return" ++ varlist nv , y , fs3+b)
printMorph s v fs (Op m i (Func c n)) =
    let (ms , mv , fs2) = printMorph s v fs m in
    let (a , b) = typeMorph n in
    let (x , _) = takeL i a mv in
    let (ns , nv , fs3) = printMorph ("  " ++ s) x fs2 n in
    let f = [fs3 .. (fs3+b-1)] in
    let (_ , y) = repL i a mv f in
        (ms ++ "\n" ++ s ++ show f ++ " <-" ++ c ++ "-" ++ ns ++ "\n" ++ s ++ "  return" ++ varlist nv , y , fs3+b)

--printMorph _ _ _ _ = ("" , [] , 0)

printMorphE :: String -> [Int] -> Int -> Morph -> String
printMorphE s v fs m = let (q , w , _) = printMorph s v fs m in
    q ++ "\n" ++ s ++ "return" ++ varlist w


-- ======================================
-- Basic utility on the Morphism datatype
-- ======================================

isOp :: Morph -> Maybe (Int , Oper , Morph)
isOp (Start _) = Nothing
isOp (Op m i o) = Just (i , o , m)

typeOper :: Oper -> (Object , Object)
typeOper (Base (Sig _ _ i o)) = (i , o)
typeOper (Comp m _) = typeMorph (rewMorph m)
typeOper (Func _ m) = typeMorph m

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

-- checks if the next two Options are independent
squeezeMorph :: Morph -> Bool
squeezeMorph (Op (Op _ j p) i o ) =
    let (ii , _) = typeOper o in
    let (_ , jo) = typeOper p in
        ((j + jo) <= i || (i + ii) <= j) && (i /= j || ii /= 0 || jo /= 0)
squeezeMorph _ = False

squeezerMorph :: Morph -> Maybe (Int , Int , Int , Int)
squeezerMorph (Op (Op _ j p) i o ) =
    let (ii , io) = typeOper o in
    let (ji , jo) = typeOper p in
    if ((j + jo) <= i) && (i /= j || ii /= 0 || jo /= 0) 
    then 
        Just (ji - jo , 0 , 0 , io - ii)
    else 
    if ((i + ii) <= j) && (i /= j || ii /= 0 || jo /= 0)  
    then
        Just (0 , ji - jo , io - ii , 0)  
    else 
        Nothing 
squeezerMorph _ = Nothing

-- size with squeezes
--sizeMorph :: Morph -> Float
--sizeMorph (Start _) = wirerat
--sizeMorph (Op m i o) = if squeezeMorph (Op m i o) then sizeOper o + sizeMorph m else wirerat + sizeOper o + sizeMorph m

-- size without sequeezes
--sizeMorph' :: Morph -> Float
--sizeMorph' (Start _) = wirerat
--sizeMorph' (Op m _ o) = wirerat + sizeOper o + sizeMorph' m

sizeMorph'' :: Morph -> Float
sizeMorph'' (Start _) = wirerat
sizeMorph'' (Op m p o) = wirerat + sizeOper o + sizeMorph'' m - (if squeezeMorph (Op m p o) then wirerat else 0)

sizeOper :: Oper -> Float
sizeOper (Base {}) = 1
sizeOper (Comp _ m) = 1 + wirerat + 0.1 * sizeMorph'' m
--sizeOper (Comp {}) = 2 + wirerat
sizeOper (Func _ m) = 0.7 * sizeMorph'' m -- + wirerat

-- Basic coordinates of nodes in morphism
coorMorph :: Morph -> [(Float , Float)]
coorMorph m = coorMorphAlt' wirerat (sizeMorph'' m) m (0 , 0)
    --coorMorph' wirerat (sizeMorph'' m) m

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

coorMorphAlt' :: Float -> Float -> Morph -> (Int , Int) -> [(Float , Float)]
coorMorphAlt' _ _ (Start _) _ = []
coorMorphAlt' posx width (Op m i o) (dx , dy) =
    let c = sizeOper o in
    case squeezerMorph (Op m i o) of
    Just (di , dr , dj , dl) ->
        let (_ , mo) = typeMorph m in
        let (bi , bo) = typeOper o in
        let coorm = coorMorphAlt' (posx+c) width m (dj , dl) in
        let x = 1 - ((posx + c/2) / width) in
        let y = frac2Float (2 + 4*i + bi + bo       + (di + dx) ,                 -- 2 + 4*i + (bi + bo) 
                            4 + 4*mo - 2*bi + 2*bo  + (di + dr + dx + dy)) in    -- 2 + 4*i + (bi + bo) + (bi + bo) + 4*j + 2 = 4 + 4*m - 2*bi + 2*bo
        ((x , y) : coorm)                                       -- m = i + bi + j
    Nothing ->
        let coorm = coorMorphAlt' (posx+c+wirerat) width m (0 , 0) in
        let (_ , mo) = typeMorph m in
        let (bi , bo) = typeOper o in
        let x = 1 - ((posx + c/2) / width) in
        let y = frac2Float (2 + 4*i + bi + bo       + dx , 
                            4 + 4*mo - 2*bi + 2*bo  + (dx + dy)) in
        ((x , y) : coorm)
    --let squ = squeezeMorph (Op m i o) in
    --let nexx = if squ then posx+c else posx+c+wirerat in

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
operMorph (Func c m) = let (mi , _) = typeMorph m in  Op (Start mi) 0 (Func c m)

mergeOper  :: (Int , Oper) -> (Int , Oper) -> (Int , Oper)
mergeOper (i , o) (j , p) =
    let (k , q) = mergeMorph (i , operMorph o) (j , operMorph p) in
    let m = cleanMorph q in (k , Comp (RI m) m)

checkMerge :: Morph -> Maybe Morph
checkMerge (Op _ _ (Comp (RS {}) _)) = Nothing
checkMerge (Op (Op _ _ (Comp (RS {}) _)) _ _) = Nothing
checkMerge (Op (Op m j p) i o) = let (k , q) = mergeOper (i , o) (j , p) in Just (Op m k q)
checkMerge _ = Nothing

mergeIndex :: Morph -> Int -> Maybe Morph
mergeIndex (Start _) _              =   Nothing
mergeIndex (Op (Start _) _ _) _     =   Nothing
mergeIndex (Op (Op m a op) b qp) i
    |   i <= 0      =   let (c , n) = mergeMorph (b , operMorph qp) (a , operMorph op) in
                        Just (Op m c (Comp (RI n) n))
    |   otherwise   =   mergeIndex (Op m a op) (i-1) >>= \n -> Just (Op n b qp)


-- Rewrite: 
rewriteNode :: (Rew -> Morph -> Rew) -> (Float , Float) -> Float -> Morph -> [(Float , Float , Bool)] -> Morph
rewriteNode _ _ _ (Start i) _ = Start i
rewriteNode _ _ _ (Op i o m) [] = Op i o m
rewriteNode f (mx , my) bs (Op m i o) ((x , y , _) : r)
    |   abs (mx-x) <= 2*bs && abs (my-y) <= 2*bs   =  case o of
            Comp n nh           ->  Op m i (Comp (f n nh) nh)
            op                  ->  let n = operMorph op  in
                                    let p = f (RI n) n in Op m i (Comp p n)
    |   otherwise   =   let n = rewriteNode f (mx , my) bs m r in Op n i o

morphOps :: Morph -> [Sig]
morphOps (Start _) = []
morphOps (Op m _ (Base s)) = addSet s (morphOps m)
morphOps (Op m _ (Comp n _)) = joinSet (morphOps (rewMorph n)) (morphOps m)
morphOps (Op m _ (Func _ n)) = joinSet (morphOps n) (morphOps m)

-- Checks if there are comp boxes in the morphism
flatMorph :: Morph -> Bool
flatMorph (Start _) = True
flatMorph (Op m _ (Base {})) = flatMorph m
flatMorph (Op _ _ (Comp _ _)) = False
flatMorph (Op m _ (Func _ n)) = flatMorph m && flatMorph n

eqMorph :: Morph -> Morph -> Bool
eqMorph m n = cleanMorph m == cleanMorph n
eqMorph m n = insertSort m == insertSort n

-- unfolders 
unfoldPreMorph :: Morph -> Morph
unfoldPreMorph m =
    let (a , _) = typeMorph m in
        unfoldPreMorph' (Start a) m 0

unfoldPreMorph' :: Morph -> Morph -> Int -> Morph
unfoldPreMorph' m (Start _) _ = m
unfoldPreMorph' m (Op n j (Base (Sig c s a b))) i =
    Op (unfoldPreMorph' m n i) (i + j) (Base (Sig c s a b))
unfoldPreMorph' m (Op n j (Comp _ k)) i =
    unfoldPreMorph' (unfoldPreMorph' m n i) k (i + j)
unfoldPreMorph' m _ _ = m

unfoldPostMorph :: Morph -> Morph
unfoldPostMorph m =
    let (a , _) = typeMorph m in
        unfoldPostMorph' (Start a) m 0

unfoldPostMorph' :: Morph -> Morph -> Int -> Morph
unfoldPostMorph' m (Start _) _ = m
unfoldPostMorph' m (Op n j (Base (Sig c s a b))) i =
    Op (unfoldPostMorph' m n i) (i + j) (Base (Sig c s a b))
unfoldPostMorph' m (Op n j (Comp (RS _ k _ _) _)) i =
    unfoldPreMorph' (unfoldPostMorph' m n i) k (i + j)
unfoldPostMorph' m (Op n j (Comp (RI k) _)) i =
    unfoldPreMorph' (unfoldPostMorph' m n i) k (i + j)
unfoldPostMorph' m _ _ = m

unfoldInfo :: Morph -> (MR , String , Why)
unfoldInfo (Start _) = (MEqual , "?" , Axiom)
unfoldInfo (Op _ _ (Comp (RS mr _ name why) _)) = (mr , name  , why)
unfoldInfo (Op n _ _) = unfoldInfo n

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

-- ============
-- NEW
addredrule :: Ord a => (a -> a -> Bool) -> (a , a) -> [(a , a)] -> [(a , a)]
addredrule _ (x , y) [] = [(x , y)]
addredrule f (x , y) ((z , w) : l)
    |   x < z       =   (x , y) : (z , w) : l
    |   x > z       =   (z , w) : addredrule f (x , y) l
    |   f w y       =   (x , y) : l
    |   otherwise   =   (z , w) : l

allredrule :: Ord a => (a -> a -> Bool) -> [[a]] -> [(a , a)]
allredrule _ [] = []
allredrule f ([] : l) = allredrule f l
allredrule f ((a : r) : l) = allredrule' f r a l

allredrule' :: Ord a => (a -> a -> Bool) -> [a] -> a -> [[a]] -> [(a , a)]
allredrule' f [] _ l = allredrule f l
allredrule' f (a : r) b l
    |   f a b       =   addredrule f (a , b) (allredrule' f r b l)
    |   otherwise   =   allredrule' f r b l


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


-- keep sorting and remember 
keepIndex :: Int -> Morph -> [Int]
keepIndex _ (Start _) = []
keepIndex i (Op m _ _) = keepIndex (i+1) m ++ [i]

-- we use a counter to prevent diverging algorithms
keepSorting :: Morph -> (Morph , [Int])
keepSorting m =
    let v = lengthMorph m in
    let ind = keepIndex 0 m in
    keepSort (v * v) m ind (m , ind)

keepSort :: Int -> Morph -> [Int] -> (Morph , [Int]) -> (Morph , [Int])
keepSort i m l reco
    |   i <= 0      =   reco
    |   otherwise   =   case keepSort' m l reco of
            Just (reco' , n , r)    ->  keepSort (i-1) n r reco'
            Nothing ->  reco

keepSort' :: Morph -> [Int] -> (Morph , [Int]) -> Maybe ((Morph , [Int]) , Morph , [Int])
keepSort' (Op (Op m j p) i o) (a : b : l) (recm , recp) =
    let (io , oo) = typeOper o in
    if (i + io) <= j
    then
        case keepSort' (Op m i o) (a : l) (Op m i o , a : l) of
            Just ((x , y) , n , r)  ->  let (newm , newl) = (Op n (j - io + oo) p , b : r) in
                                        let (newx , newy) = (Op x (j - io + oo) p , b : y) in
                                        if not (orderMorph newx recm) then Just ((newx , newy) , newm , newl)
                                        else Just ((recm , recp) , newm , newl)
            Nothing                 ->  let (newm , newl) = (Op (Op m i o) (j - io + oo) p , b : a : l) in
                                        if not (orderMorph newm recm) then Just ((newm , newl) , newm , newl)
                                        else Just ((recm , recp) , newm , newl)
    else keepSort' (Op m j p) (b : l) (Op m j p , b : l) >>= \((x , y) , m' , l') ->
                                        let (newm , newl) = (Op m' i o , a : l') in
                                        let (newx , newy) = (Op x i o , a : y) in
                                        if not (orderMorph newx recm) then Just ((newx , newy) , newm , newl)
                                        else Just ((recm , recp) , newm , newl)
keepSort' _ _ _ = Nothing


-- we need allsort: but whatever

addMall :: (Morph , [Int]) -> [(Morph , [Int])] -> Maybe [(Morph , [Int])]
addMall (m , l) [] = Just [(m , l)]
addMall (m , l) ((n , r) : p)
    |   m == n          =   Nothing
    |   orderMorph n m  =   Just ((m , l) : (n , r) : p)
    |   otherwise       =   fmap ((n , r) :) (addMall (m , l) p)

addMalls :: [(Morph , [Int])] -> [(Morph , [Int])] -> ([(Morph , [Int])] , [(Morph , [Int])])
addMalls [] his = ([] , his)
addMalls ((m , l) : p) his =
    let (p' , his') = addMalls p his in
    case addMall (m , l) his' of
        Just his''  ->  ((m , l) : p' , his'')
        Nothing     ->  (p' , his')


interMall :: Morph -> [Int] -> [(Morph , [Int])]
interMall (Op (Op m j p) i o) (a : b : l) =
    let reco = interMall (Op m j p) (b : l) in
    let reco' = fmap (\(x , y) -> (Op x i o , a : y)) reco in
    let (io , oo) = typeOper o in
    if (i + io) <= j    then (Op (Op m i o) (j - io + oo) p , b : a : l) : reco'
                        else    reco'
interMall _ _ = []

tryMall :: Int -> [(Morph , [Int])] -> [(Morph , [Int])] -> [(Morph , [Int])]
tryMall _ [] his = his
tryMall i ((m , l) : new) his 
    |   i <= 0      =   his
    |   otherwise   = 
        let gog = interMall m l in
        -- if no interchanges possible, m is in normal form, and we are done
        if null gog then [(m , l)] else
        let (x , his') = addMalls gog his in
            tryMall (i-1) (x ++ new) his'

sortMall :: Morph -> (Morph , [Int])
sortMall m =
    let v = lengthMorph m in
    let l = keepIndex 0 m in
    let reco = tryMall (v * v) [(m , l)] [(m , l)] in
    case reco of
        (w : _)     ->  w
        _           ->  (m , l)

--allSort :: [(Morph , [Int])] -> [(Morph , [Int])] -> [(Morph , [Int])]


--keepSorting :: Morph -> [Int] -> (Morph , [Int])

--sortRelat :: Relat -> Relat
--sortRelat (x , m , n , t) = (x , insertSort m , insertSort n , t)

cleanRelat :: Relat -> Relat
cleanRelat (x , m , n , t , w) = (x , cleanMorph m , cleanMorph n , t , w)

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


-- remember knay
knayMorphRem :: Morph -> (Morph , [Int])
knayMorphRem m =
    let (i , v) = listMorph m in
    let l = foldRem 0 v in
    let r = layersKnayRem i 0 False l in
    let p = (i , fmap (\(x , y , _) -> (x , y)) r) in
    let c = splitRem r in
        (buildMorph p , c)

foldRem :: Int -> [(Object , Oper)]-> [(Object , Oper , Int)]
foldRem _ [] = []
foldRem a ((j , o) : l) = (j , o , a) : foldRem (a+1) l

splitRem :: [(Object , Oper , Int)] -> [Int]
splitRem [] = []
splitRem ((_ , _ , a) : l) = a : splitRem l

layersKnayRem :: Int -> Int -> Bool -> [(Object , Oper , Int)] -> [(Object , Oper , Int)]
layersKnayRem _ _ _ [] = []
layersKnayRem h i k ((j , o , a) : l) =
    case layerKnayRem h i ((j , o , a) : l) of
        Just ((q , b) , r)
                        ->  let (iq , oq) = typeOper q in
                            (i , q , b) : layersKnayRem (h-iq+oq) (i+oq) True r
        Nothing         ->  let (io , oo) = typeOper o in
                            if i >= h then
                                if k then layersKnayRem h 0 False ((j , o , a) : l)
                                else (j , o , a) : layersKnayRem (h-io+oo) (i+oo) True l
                            else layersKnayRem h (i+1) k ((j , o , a) : l)

layerKnayRem :: Int -> Int -> [(Object , Oper , Int)] -> Maybe ((Oper , Int) , [(Object , Oper , Int)])
layerKnayRem _ _ [] = Nothing
layerKnayRem h i ((j , o , a) : l)
    |   i == j && fst (typeOper o) > 0
                        =   Just ((o , a) , l)
    |   i >= h          =   Nothing
    |   i < j           =   let (io , oo) = typeOper o in
                            layerKnayRem (h-io+oo) i l >>= \((q , b) , r) ->
                            let (iq , oq) = typeOper q in
                            if (i + iq) > j then Nothing else Just ((q , b) , (j-iq+oq , o , a) : r)
    |   otherwise       =   let (io , oo) = typeOper o in
                            if i < (j + io) then Nothing else
                            layerKnayRem (h-io+oo) (i-io+oo) l >>= \((q , b) , r) ->
                            Just ((q , b) , (j , o , a) : r)

-- =====================
-- Schematic alterations
-- =====================

lookupDict :: Ord a => [(a , b)] -> a -> Maybe b
lookupDict [] _ = Nothing
lookupDict ((a , b) : l) a'
    |   a' < a      =   Nothing
    |   a' == a     =   Just b
    |   otherwise   =   lookupDict l a'

lookupDictU :: Ord a => b -> [(a , b)] -> a -> b
lookupDictU b l a = case lookupDict l a of
    Just b'     ->  b'
    _           ->  b

updateDict :: Ord a => [(a , b)] -> (a , b) -> [(a , b)]
updateDict [] (a , b) = [(a , b)]
updateDict ((a , b) : l) (a' , b')
    |   a' < a      =   (a' , b') : (a , b) : l
    |   a' == a     =   (a' , b') : l
    |   otherwise   =   (a , b) : updateDict l (a' , b')

updatesDict :: Ord a => [(a , b)] -> [(a , b)] -> [(a , b)]
updatesDict l r = foldl updateDict r l

cleanDict ::  Ord a => [(a , b)] -> [(a , b)]
cleanDict [] = []
cleanDict (x : l) = updateDict (cleanDict l) x

mergeDict :: Ord a => [(a , b)] -> [(a , b)] -> [(a , b)]
mergeDict [] r = r
mergeDict l [] = l
mergeDict ((a , b) : l) ((a' , b') : r)
    |   a' < a      =   (a' , b') : mergeDict l ((a' , b') : r)
    |   a' > a      =   (a , b) : mergeDict ((a , b) : l) r
    |   otherwise   =   (a , b) : mergeDict l r

-- Toggle Move 
toggleMorph :: [(Sig, Sig)] -> Morph -> Maybe Morph
toggleMorph _ (Start i) = Just (Start i)
toggleMorph dict (Op m i (Base s)) =
    toggleMorph dict m >>= \m' ->
    lookupDict dict s >>= \s' ->
        Just (Op m' i (Base s'))
toggleMorph _ _ = Nothing

toggleRelat ::  [(Sig , Sig)] -> Relat -> Maybe Relat
toggleRelat dict (e , m , n , s , w) =
    toggleMorph dict m >>= \m' ->
    toggleMorph dict n >>= \n' ->
        Just (e , m' , n' , "T(" ++ uptoBar s ++ ")" , w)

-- Flipping morphism upside down 
flipMorph :: [(Sig , Sig)] -> Morph -> Maybe (Morph , Int)
flipMorph _ (Start i) = Just (Start i , i)
flipMorph dict (Op m i (Base s)) =
    flipMorph dict m >>= \(m' , j) ->
    lookupDict dict s >>= \s' ->
    let Sig _ _ inp out = s' in
        Just (Op m' (j - i - inp) (Base s') , j - inp + out)
flipMorph _ _ = Nothing

flipRelat ::  [(Sig , Sig)] -> Relat -> Maybe Relat
flipRelat dict (e , m , n , s , w) =
    flipMorph dict m >>= \(m' , _) ->
    flipMorph dict n >>= \(n' , _) ->
        Just (e , m' , n' , "F(" ++ uptoBar s ++ ")" , w)

mapLMorph :: [(Sig , Sig)] -> [(Object , Oper)] -> Maybe [(Object , Oper)]
mapLMorph _ [] = Just []
mapLMorph dict ((i , Base s) : l) =
    lookupDict dict s >>= \s' ->
    fmap ((i , Base s') :) (mapLMorph dict l)
mapLMorph _ _ = Nothing

mirrorMorph :: [(Sig , Sig)] -> Morph -> Maybe Morph
mirrorMorph dict m =
    let (_ , mo) = typeMorph m in
    let (_ , lis) = listMorph m in
    mapLMorph dict lis >>= \lis' ->
        Just (buildMorph (mo , reverse lis'))

mirrorRelat ::  [(Sig , Sig)] -> Relat -> Maybe Relat
mirrorRelat dict (e , m , n , s , w) =
    mirrorMorph dict m >>= \m' ->
    mirrorMorph dict n >>= \n' ->
        Just (e , m' , n' , "M(" ++ uptoBar s ++ ")" , w)

lastbox :: Morph -> Morph -> Morph
lastbox m (Start _) = m
lastbox _ (Op _ _ (Comp _ k)) = k
lastbox m (Op n _ _) = lastbox m n

boxIt :: Morph -> Morph
boxIt m = let (i , _) = typeMorph m in Op (Start i) 0 (Comp (RI m) m)

functify :: Morph -> Morph
functify (Start i) = Start i
functify (Op m i (Comp _ x)) = Op (functify m) i (Func "I" x)
functify (Op m i op) = Op (functify m) i op


matchOp :: Oper -> Oper -> Maybe [(Char, Exp)]
matchOp (Base (Sig nam (Nothing , _) a b)) (Base (Sig nam' (Nothing , _) a' b'))
    |   nam == nam' && a == a' && b == b'   =   Just []
matchOp (Base (Sig nam (Just ex , _) a b)) (Base (Sig nam' (Just ex' , _) a' b'))
    |   nam == nam' && a == a' && b == b'   =   matchExp ex ex'
matchOp _ _ = Nothing

matchaMorph :: Morph -> Morph -> Maybe [(Char, Exp)]
matchaMorph (Start i) (Start j)
    |   i == j      =   Just []
    |   otherwise   =   Nothing
matchaMorph (Start _) _ = Nothing
matchaMorph _ (Start _) = Nothing
matchaMorph (Op m i op) (Op n j qp)
    |   i == j  =   matchOp op qp >>= \l -> matchaMorph m n >>= \r -> addSubsts l r
    |   otherwise   =   Nothing

substOp :: Oper -> [(Char, Exp)] -> Maybe Oper
substOp (Base (Sig nam (Nothing , style) a b)) _ = Just (Base (Sig nam (Nothing , style) a b))
substOp (Base (Sig nam (Just ex , style) a b)) sub = substExp ex sub >>= \ex' -> Just (Base (Sig nam (Just ex' , style) a b))
substOp _ _ = Nothing

substMorph :: Morph -> [(Char, Exp)] -> Maybe Morph
substMorph (Start i) _ = Just (Start i)
substMorph (Op m i op) sub = substOp op sub >>= \op' -> substMorph m sub >>= \m' -> Just (Op m' i op')

matcherMorph :: Morph -> Morph -> Maybe (Morph -> Maybe Morph)
matcherMorph m n = matchaMorph m n >>= \sub -> Just (`substMorph` sub)


opinMorph :: Char -> Morph -> Bool
opinMorph _ (Start _) = False
opinMorph c (Op m _ (Base (Sig d _ _ _))) = c == d || opinMorph c m
opinMorph c (Op m _ (Comp _ n)) = opinMorph c n || opinMorph c m
opinMorph c (Op m _ (Func _ n)) = opinMorph c n || opinMorph c m


typeMatch :: Morph -> Morph -> Bool
typeMatch m n = typeMorph m == typeMorph n

checkMorph :: Morph -> Maybe Int
checkMorph (Start i) = return i
checkMorph (Op m i op) =
    checkMorph m >>= \mo ->
    let (a , b) = typeOper op in
    if (i+a) <= mo then Just (mo-a+b) else Nothing


bringWire :: Morph -> Int -> Int -> Morph
bringWire m i j
    |   i > j       =   bringWire (Op m (i-1) (Base (Sig 'x' (Nothing , "1") 2 2))) (i-1) j
    |   otherwise   =   m

copyWires :: Morph -> Int -> Int -> Int -> Morph
copyWires m i j k
    |   i <= j      =   copyWires (bringWire (Op m i (Base (Sig 'c' (Nothing , "2") 1 2))) i k) (i+2) (j+1) (k+1)
    |   otherwise   =   m

deleteWires :: Morph -> Int -> Int -> Morph
deleteWires m i j
    |   i < j       =   deleteWires (Op m i (Base (Sig 'd' (Nothing , "2") 1 0))) i (j-1)
    |   otherwise   =   m

copyMorph :: Morph -> Morph
copyMorph m =
    let (cm , ca) = (copyMorph' m) in
    let (_ , mo) = typeMorph m in
        deleteWires cm ca (ca + mo)

copyMorph' :: Morph -> (Morph , Int)
copyMorph' (Start a) = (copyWires (Start a) 0 (a-1) 0 , a)
copyMorph' (Op m i o) =
--   let (_ , mo) = typeMorph m in 
   let (_ , oo) = typeOper o in
   let (cm , ca) = copyMorph' m in
       (copyWires (Op cm (ca + i) o) (ca + i) (ca + i + oo - 1) ca , ca + oo)
