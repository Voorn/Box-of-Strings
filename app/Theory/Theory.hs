module Theory.Theory where

import Morph

-- S

-- ==========================================================
-- Theory module: contains generic relation types and schemas
-- ==========================================================


-- Data type of basic relation types
data Basic =
    --  Swap  x   s :   have Option s dragged across swap Option x
        Swap Sig Sig
    --  Dist  x   f   g :   Distribute f over g, using x as swap Option
    |   Dist Sig Sig Sig MR

-- Data type of schema types
data Schema =
    --  Symmetry x: have all Options be draggable across swap Option x
        Symmetry Sig (Maybe [Sig])
    --  Naturality  x   s : Every diagram distributes over s, using x as swap
    |   Naturality Sig Sig MR (Maybe [Sig])
    --  Naturality  x   s : Every diagram distributes over s, using x as swap
    |   If Sig Sig Sig Sig (Maybe [Sig])
    --  Flipping upside down
    |   Flip [(Sig , Sig)]
    --  Mirroring left to right
    |   Mirror [(Sig , Sig)]
    --  Toggle operations
    |   Toggle [(Sig , Sig)]
    deriving (Eq , Show)

-- For Schema, there are optional argument [Sig] which declare a set of allowed operations


flushSig :: String -> [Sig] -> [Sig]
flushSig _ [] = []
flushSig c ((Sig d style a b) : l)
    |   c == d      =   flushSig c l
    |   otherwise   =   Sig d style a b : flushSig c l

flushSigs :: String -> [(Sig , Sig)] -> [(Sig , Sig)]
flushSigs _ [] = []
flushSigs c ((Sig d style a b , Sig d' style' a' b') : l)
    |   c == d || c == d'   =   flushSigs c l
    |   otherwise           =   (Sig d style a b , Sig d' style' a' b') : flushSigs c l


flushSchema :: String -> [Schema] -> [Schema]
flushSchema _ [] = []
flushSchema c (Symmetry s rest : l)
    |   c == nameSig s  =   flushSchema c l 
    |   otherwise       =   Symmetry s (fmap (flushSig c) rest) : flushSchema c l 
flushSchema c (Naturality s z moder rest : l)
    |   c == nameSig s || c == nameSig z    =   flushSchema c l 
    |   otherwise   =   Naturality s z moder (fmap (flushSig c) rest) : flushSchema c l 
flushSchema c (If s z v w rest : l)
    |   c == nameSig s || c == nameSig z || 
        c == nameSig v || c == nameSig w    =   flushSchema c l 
    |   otherwise                           =   If s z v w (fmap (flushSig c) rest) : flushSchema c l 
flushSchema c (Flip pairs : l)  =   Flip (flushSigs c pairs) : flushSchema c l
flushSchema c (Mirror pairs : l)  =   Mirror (flushSigs c pairs) : flushSchema c l
flushSchema c (Toggle pairs : l)  =   Toggle (flushSigs c pairs) : flushSchema c l

upSwap :: Sig -> Morph -> Int -> Int -> Morph
upSwap s m i j
    |   i >= j      =   upSwap s (Op m i (Base s)) (i-1) j
    |   otherwise   =   m

downSwap :: Sig -> Morph -> Int -> Int -> Morph
downSwap s m i j
    |   i <= j      =   downSwap s (Op m i (Base s)) (i+1) j
    |   otherwise   =   m


-- The weave
theWeave :: Sig -> Int -> Int -> Morph -> Morph
theWeave x a b m = theWeaver x m 0 a b 1

-- 0 2 2 1
theWeaver :: Sig -> Morph -> Int -> Int -> Int -> Int -> Morph
theWeaver x m bas num spl ind
    |   spl > 1 && ind < num        =   theWeaver x (upSwap x m (bas + ind*spl-1) (bas + ind)) bas num spl (ind + 1)
    |   spl > 1                     =   theWeaver x m (bas+num) num (spl-1) 1
    |   otherwise                   =   m

repeatSig :: Oper -> Int -> Morph -> Morph
repeatSig g i m = 
    let (_ , b) = typeOper g in repeater g i m b

repeater :: Oper -> Int -> Morph -> Int -> Morph
repeater s i m a
    |   i > 0       =   Op (repeater s (i-1) m a) ((i-1)*a) s
    |   otherwise   =   m

cohereSig :: Sig -> Oper -> Int -> Morph -> Morph
cohereSig x g i m = 
    let (a , b) = typeOper g in theWeave x i b (repeatSig g i (theWeave x a i m))

--      -f-- -      - --f-
--          g   =    g
--      -f-- -      - --f-
distribSig :: Sig -> Oper -> Oper -> Morph
distribSig x f g =
    let (fa , fb) = typeOper f in
    let (ga , _) = typeOper g in
    cohereSig x g fb (repeatSig f ga (Start (fa*ga)))

distribSig2 :: Sig -> Oper -> Oper -> Morph
distribSig2 x f g =
    let (fa , _) = typeOper f in
    let (ga , gb) = typeOper g in
    repeatSig f gb (cohereSig x g fa (Start (fa*ga)))

distribEqu :: Sig -> Oper -> Oper -> MR -> Relat
distribEqu x f g mt = (mt , distribSig x f g , distribSig2 x f g , "Dist(" ++ nameSig x ++ ',' : nameOper f ++ ',' : nameOper g ++ ")" , Axiom)

ifSig1 :: Sig -> Sig -> Int -> Int -> Morph -> Morph 
ifSig1 c d i r m 
    -- this first case should only be called if  i = 0
    |   r <= 0      =   Op m 0 (Base d)
    |   r == 1      =   m
    |   otherwise   =   Op (ifSig1 c d i (r-1) m) i (Base c)

ifSig2 :: Sig -> Sig -> Sig -> Sig -> Int -> Morph -> Morph 
ifSig2 x c d i k m = repeatSig (Base i) k (theWeave x 3 k (ifSig1 c d k k m))

ifSigL :: Sig -> Sig -> Sig -> Sig -> Oper -> Morph 
ifSigL x copy discard phi f = 
    let (a , b) = typeOper f in
    ifSig2 x copy discard phi b (Op (Op (Start (2*a + 1)) 0 f) (b+1) f)

ifSigR :: Sig -> Sig -> Sig -> Sig -> Oper -> Morph 
ifSigR x copy discard phi f =
    let (a , _) = typeOper f in 
    Op (ifSig2 x copy discard phi a (Start (2*a + 1))) 0 f

ifEqu :: Sig -> Sig -> Sig -> Sig -> Oper -> Relat 
ifEqu x c d p f = 
    let (a , b) = typeOper f in 
        (MEqual , ifSigL x c d p f , ifSigR x c d p f , "If(" ++ nameOper f ++ ")" , Axiom)

--      -f- -     - ---
--         X   =   X
--      --- -     - -f-
symmetryDown :: Sig -> Oper -> Relat
symmetryDown x op =
    let (i , o) = typeOper op in
    (MEqual ,
    upSwap x (Op (Start (i+1)) 0 op) (o-1) 0 ,
    Op (upSwap x (Start (i+1)) (i-1) 0) 1 op ,
    "SymD(" ++ nameSig x ++ ',' : nameOper op ++ ")" ,
    Axiom)

symmetryUp :: Sig -> Oper -> Relat
symmetryUp x op =
    let (i , o) = typeOper op in
    (MEqual ,
    downSwap x (Op (Start (i+1)) 1 op) 0 (o-1) ,
    Op (downSwap x (Start (i+1)) 0 (i-1)) 0 op ,
    "SymU(" ++ nameSig x ++ ',' : nameOper op ++ ")",
    Axiom)

symmetryAdd :: Sig -> Oper -> [Relat]
symmetryAdd x s = [symmetryDown x s , symmetryUp x s]



addCompOp :: Sig -> [Sig] -> [Schema] -> [Schema]
addCompOp _ _ [] = []
addCompOp s sub (Symmetry x Nothing : l) = Symmetry x Nothing : addCompOp s sub l
addCompOp s sub (Symmetry x (Just k) : l)
    |   subSet sub k    =   Symmetry x (Just (addSet s k)) : addCompOp s sub l
    |   otherwise       =   Symmetry x (Just k) : addCompOp s sub l
addCompOp s sub (Naturality x y moder Nothing : l) = Naturality x y moder Nothing : addCompOp s sub l
addCompOp s sub (Naturality x y moder (Just k) : l)
    |   subSet sub k    =   Naturality x y moder (Just (addSet s k)) : addCompOp s sub l
    |   otherwise       =   Naturality x y moder (Just k) : addCompOp s sub l
addCompOp s sub (If x c d p Nothing : l) = If x c d p Nothing : addCompOp s sub l
addCompOp s sub (If x c d p (Just k) : l)
    |   subSet sub k    =   If x c d p (Just (addSet s k)) : addCompOp s sub l
    |   otherwise       =   If x c d p (Just k) : addCompOp s sub l
addCompOp s sub (Flip a : l) = Flip a : addCompOp s sub l
addCompOp s sub (Mirror a : l) = Mirror a : addCompOp s sub l
addCompOp s sub (Toggle a : l) = Toggle a : addCompOp s sub l


-- =======================================
-- Adding basic relations and using schema
-- =======================================

newBasic :: Basic -> [Relat]
newBasic (Swap x s) = symmetryAdd x (Base s)
newBasic (Dist x f g moder) = [distribEqu x (Base f) (Base g) moder]

useSchema :: Schema -> Sig -> [Relat]
useSchema (Symmetry x Nothing)  f       =   symmetryAdd x (Base f)
useSchema (Symmetry x (Just l)) f
    |   inSet f l                       =   symmetryAdd x (Base f)
    |   otherwise                       =   []
useSchema (Naturality x f moder Nothing)  g   =
            [distribEqu x (Base f) (Base g) (reverseMR moder) , distribEqu x (Base g) (Base f) moder]
useSchema (Naturality x f moder (Just l)) g
    |   inSet g l                       =
            [distribEqu x (Base f) (Base g) (reverseMR moder) , distribEqu x (Base g) (Base f) moder]
    |   otherwise                       =   []
useSchema (If x c d p Nothing)  g   =
            [ifEqu x c d p (Base g)]
useSchema (If x c d p (Just l)) g
    |   inSet g l                       =
            [ifEqu x c d p (Base g)]
    |   otherwise                       =   []
useSchema (Flip _) _ = []
useSchema (Mirror _) _ = []
useSchema (Toggle _) _ = []

funcSchema :: Schema -> String -> Morph -> [Relat]
funcSchema (Symmetry x Nothing) cF f      =   symmetryAdd x (Func cF f)
funcSchema (Symmetry x (Just l)) cF f
    |   subSet (morphOps f) l           =   symmetryAdd x (Func cF f)
    |   otherwise                       =   []
funcSchema (Naturality x f moder Nothing) cF g   =
            [distribEqu x (Base f) (Func cF g) (reverseMR moder) , distribEqu x (Func cF g) (Base f) moder]
funcSchema (Naturality x f moder (Just l)) cF g
    |   subSet (morphOps g) l                     =
            [distribEqu x (Base f) (Func cF g) (reverseMR moder) , distribEqu x (Func cF g) (Base f) moder]
    |   otherwise                       =   []
funcSchema (If x c d p Nothing) cF g   =
            [ifEqu x c d p (Func cF g)]
funcSchema (If x c d p (Just l)) cF g
    |   subSet (morphOps g) l                      =
            [ifEqu x c d p (Func cF g)]
    |   otherwise                       =   []
funcSchema (Flip _) _ _ = []
funcSchema (Mirror _) _ _ = []
funcSchema (Toggle _) _ _ = []

newSchema :: Schema -> [Sig] -> [Relat]
newSchema _ [] = []
newSchema schema (s : sig)    = newSchema schema sig ++ useSchema schema s

newOp :: [Schema] -> Oper -> [Relat]
newOp (schema : l) (Base s) = remRelat (useSchema schema s) ++ newOp l (Base s)
newOp (schema : l) (Func c m) = remRelat (funcSchema schema c m) ++ newOp l (Func c m)
newOp _ _ = []

sieveRelat :: [Relat] -> [Relat]
sieveRelat [] = []
sieveRelat ((mode , m , n , name , w) : l)
    |   m == n      =   sieveRelat l 
    |   otherwise   =   (mode , m , n , name , w) : sieveRelat l

useSchema2 :: Schema -> Relat -> [Relat]
useSchema2 (Flip dict) rel = case flipRelat dict rel of
    Just rel'   ->  [rel']
    _           ->  []
useSchema2 (Mirror dict) rel = case mirrorRelat dict rel of
    Just rel'   ->  [rel']
    _           ->  []
useSchema2 (Toggle dict) rel = case toggleRelat dict rel of
    Just rel'   ->  [rel']
    _           ->  []
useSchema2 _ _ = []

newSchema2 :: Schema -> [Relat] -> [Relat]
newSchema2 _ [] = []
newSchema2 (Symmetry {}) relats = relats
newSchema2 (Naturality {}) relats = relats
newSchema2 schema (s : sig)    = s : useSchema2 schema s ++ newSchema2 schema sig

--newRelat2 :: [Schema] -> Relat -> [Relat]
--newRelat2 [] _ = []
--newRelat2 (s : l) relat = useSchema2 s relat ++ newRelat2 l relat 

newRelats ::  [Schema] -> [Relat] -> [Relat]
newRelats schem relats = foldl (flip newSchema2) relats schem
--relats ++ concatMap (newRelat2 schem) relats


alterSig :: Maybe [Sig] -> Maybe [Sig] -> Maybe [Sig]
alterSig (Just l) (Just r) = Just (joinSet l r)
alterSig a _ = a

-- When new schema is added, merge with existing schema if compatible, otherwise overwrite
alterSchema :: Schema -> Schema -> Maybe Schema
alterSchema (Symmetry x a) (Symmetry y b)
    |   x == y      =   Just (Symmetry x (alterSig a b))
    |   otherwise   =   Nothing
alterSchema (Naturality x z moder a) (Naturality y w noder b)
    |   x == y  && z == w && moder == noder
                    =   Just (Naturality x z moder (alterSig a b))
    |   otherwise   =   Nothing
alterSchema (Flip d1) (Flip d2) = Just (Flip (cleanDict (d1 ++ d2)))
alterSchema _ _     =   Nothing

addSchema :: Schema -> [Schema] -> (Schema , [Schema])
addSchema s [] = (s , [s])
addSchema s (z : l) = case alterSchema s z of
    Just k      ->  (k , k : l)
    Nothing     ->  let (x , y) = addSchema s l in (x , z : y)

--addSchemas :: [Schema] -> [Schema] -> [Schema]
--addSchemas l r = foldr addSchema r l


-- =================
-- Schema to example
-- =================

exampleSchema :: Schema -> [Relat]
exampleSchema (Symmetry x _) = symmetryAdd x (Base (Sig "-" (Nothing , "-") 2 2))
exampleSchema (Naturality x f e _) = 
    [distribEqu x (Base f) (Base (Sig "-" (Nothing , "-") 2 2)) (reverseMR e) , 
     distribEqu x (Base (Sig "-" (Nothing , "-") 2 2)) (Base f) e]
exampleSchema _ = []

exampleSchemas :: [Schema] -> [Relat]
exampleSchemas = concatMap exampleSchema