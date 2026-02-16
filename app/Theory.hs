module Theory where

import Morph


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
    deriving Show




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

repeatSig :: Sig -> Int -> Morph -> Morph
repeatSig (Sig c s a b) i m = repeater (Sig c s a b) i m a

repeater :: Sig -> Int -> Morph -> Int -> Morph
repeater s i m a
    |   i > 0       =   repeater s (i-1) (Op m ((i-1)*a) (Base s)) a
    |   otherwise   =   m

cohereSig :: Sig -> Sig -> Int -> Morph -> Morph
cohereSig x (Sig c s a b) i m = theWeave x i b (repeatSig (Sig c s a b) i (theWeave x a i m))

--      -f-- -      - --f-
--          g   =    g
--      -f-- -      - --f-
distribSig :: Sig -> Sig -> Sig -> Morph
distribSig x (Sig fc fs fa fb) (Sig gc gs ga gb) =
    cohereSig x (Sig gc gs ga gb) fb (repeatSig (Sig fc fs fa fb) ga (Start (fa*ga)))

distribSig2 :: Sig -> Sig -> Sig -> Morph
distribSig2 x (Sig fc fs fa fb) (Sig gc gs ga gb) =
    repeatSig (Sig fc fs fa fb) gb (cohereSig x (Sig gc gs ga gb) fa (Start (fa*ga)))

distribEqu :: Sig -> Sig -> Sig -> MR -> Relat
distribEqu x f g mt = (mt , distribSig x f g , distribSig2 x f g)


--      -f- -     - ---
--         X   =   X
--      --- -     - -f-
symmetryDown :: Sig -> Sig -> Relat
symmetryDown x (Sig c s i o) =
    (MEqual , 
    upSwap x (Op (Start (i+1)) 0 (Base (Sig c s i o))) (o-1) 0 ,
    Op (upSwap x (Start (i+1)) (i-1) 0) 1 (Base (Sig c s i o)))

symmetryUp :: Sig -> Sig -> Relat
symmetryUp x (Sig c s i o) =
    (MEqual , 
    downSwap x (Op (Start (i+1)) 1 (Base (Sig c s i o))) 0 (o-1) ,
    Op (downSwap x (Start (i+1)) 0 (i-1)) 0 (Base (Sig c s i o)))

symmetryAdd :: Sig -> Sig -> [Relat]
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


-- =======================================
-- Adding basic relations and using schema
-- =======================================

newBasic :: Basic -> [Relat]
newBasic (Swap x s) = symmetryAdd x s
newBasic (Dist x f g moder) = [distribEqu x f g moder]

useSchema :: Schema -> Sig -> [Relat]
useSchema (Symmetry x Nothing)  f       =   symmetryAdd x f
useSchema (Symmetry x (Just l)) f 
    |   inSet f l                       =   symmetryAdd x f
    |   otherwise                       =   []
useSchema (Naturality x f moder Nothing)  g   =   
            [distribEqu x f g (reverseMR moder) , distribEqu x g f moder]
useSchema (Naturality x f moder (Just l)) g 
    |   inSet g l                       =   
            [distribEqu x f g (reverseMR moder) , distribEqu x g f moder]
    |   otherwise                       =   []

newSchema :: Schema -> [Sig] -> [Relat]
newSchema _ [] = []
newSchema schema (s : sig)    = newSchema schema sig ++ useSchema schema s

newOp :: [Schema] -> Sig -> [Relat]
newOp (schema : l) s = remRelat (useSchema schema s) ++ newOp l s
newOp _ _ = []

-- When new schema is added, merge with existing schema if compatible, otherwise overwrite
alterSchema :: Schema -> Schema -> Maybe Schema
alterSchema (Symmetry x (Just l)) (Symmetry y (Just r))
    |   x == y      =   Just (Symmetry x (Just (joinSet l r)))
    |   otherwise   =   Nothing
alterSchema (Symmetry x a) (Symmetry y _)
    |   x == y      =   Just (Symmetry x a)
    |   otherwise   =   Nothing
alterSchema (Naturality x z moder a) (Naturality y w noder _)
    |   x == y  && z == w && moder == noder
                    =   Just (Naturality x z moder a)
    |   otherwise   =   Nothing
alterSchema _ _     =   Nothing

addSchema :: Schema -> [Schema] -> [Schema]
addSchema s [] = [s]
addSchema s (z : l) = case alterSchema s z of
    Just k      ->  k : l
    Nothing     ->  z : addSchema s l

addSchemas :: [Schema] -> [Schema] -> [Schema]
addSchemas l r = foldr addSchema r l