module Gloss.Event where

-- standard library
import Data.Maybe
import Data.Bifunctor
import Data.List

import GHC.Float
-- extended libraries
import Graphics.Gloss
import Graphics.Gloss.Interface.IO.Interact
import Graphics.Gloss.Interface.IO.Game
import Graphics.Gloss.Interface.Environment
import System.Exit
import System.Directory.Extra

-- project libraries
import Morph
import Rewrite
import Gloss.Display
import Gloss.Actions
import Parse
import Gloss.World
import HyperMatch
import Theory
import Proof
import Write

-- semantic addition
import SemanticFree
--import DSL.ProbCircDSL as ProbCirc
--import SemanticInterpreterPoly as Poly
import Evaluation
import Data.IORef
import qualified Data.Map as Map
import System.IO.Unsafe (unsafePerformIO)
import qualified Equivalence as Equiv
import qualified CodeGen
import Data.Maybe (Maybe(Just))
import qualified Data.Text.IO as T
import SemanticFree (prettySemanticClean)


{-# NOINLINE globalCompositeLib #-}
globalCompositeLib :: IORef CompositeLibrary
globalCompositeLib = unsafePerformIO (newIORef Map.empty)
{-# NOINLINE currentDSL #-}
currentDSL :: IORef String
currentDSL = unsafePerformIO (newIORef "probcirc")
-- currentDSL = unsafePerformIO (newIORef "boolean")



-- ===============
-- Event structure
-- ===============

event :: Event -> World -> IO World
event (EventKey (SpecialKey KeyEsc) Down _ _) _ = exitSuccess

-- zoom 
event (EventKey (MouseButton WheelDown) Down _ p) (Load size _ l) = return (Load (size-10) (tM (size-10) p) l)
event (EventKey (MouseButton WheelUp) Down _ p) (Load size _ l) = return (Load (size+10) (tM (size+10) p) l)

-- loading file 
event (EventKey (MouseButton LeftButton) Down _ p) (Load size _ l) =
    selectMenu False size (mouseMenu size (tM size p)) l (Load size (tM size p) l)
event (EventKey (MouseButton RightButton) Down _ p) (Load size _ l) =
    selectMenu True size (mouseMenu size (tM size p)) l (Load size (tM size p) l)
event (EventMotion p) (Load size _ l) = return (Load size (tM size p) l)
event _ (Load size p l) = return (Load size p l)

-- when transitioning, don't do anything
event (EventKey (MouseButton LeftButton) Down _ _) w     |   isTran w    =   return (interupWorld w)
event (EventKey (MouseButton LeftButton) Down _ _) w     |   isAnim w    =   return (interupWorld w)
event (EventMotion p) w     |   isTran w    =   return (updateMouse p w)
event (EventMotion p) w     |   isAnim w    =   return (updateMouse p w)
event _ w                   |   isTran w    =   return w
event _ w                   |   isAnim w    =   return w
-- when displaying
event (EventKey (MouseButton LeftButton) Down _ _) w    |   isDisp w    =   return (setMode Play w)
event (EventKey (MouseButton WheelUp) Down _ _) w       |   isDisp w    =   return (setMode (Disp (getDisp w+1)) w)
event (EventKey (MouseButton WheelDown) Down _ _) w     |   isDisp w    =   return (setMode (Disp (getDisp w-1)) w)
event (EventMotion p) w                                 |   isDisp w    =   return (updateMouse p w)
event _ w                                               |   isDisp w    =   return w
-- editor
event (EventKey (Char c) Down (Modifiers _ _ ct) _) w   |   isEdit w    =
    case wmode w of
        (Edit writ , _ , _)     ->  editorAddChar c ct w writ
        _                       ->  return w
-- semantics
event (EventKey (Char 'e') Down _ _) w = let m = morphism w in do
    dslName <- readIORef currentDSL
    lib <- readIORef globalCompositeLib
    case parseMode dslName of
        Just mode -> evaluateWithMode mode lib m
        Nothing -> putStrLn $ "Unknown DSL: " ++ dslName
    return w

event (EventKey (Char 'q') Down _ _) w@(World _ _ _ _ _ page _) = do
    dslName <- readIORef currentDSL
    lib <- readIORef globalCompositeLib
    result <- Equiv.validateCurrentPage dslName lib page
    return w


event (EventKey (Char 'w') Down _ _) w@(World _ _ _ _ _ page _) = do
    dslName <- readIORef currentDSL
    lib <- readIORef globalCompositeLib
    Equiv.validateTheoryFromPage dslName lib page
    return w

event (EventKey (Char 'h') Down _ _) w@(World m _ _ _ _ page _) = do
    dslName <- readIORef currentDSL
    lib <- readIORef globalCompositeLib
    case CodeGen.generateFromMorph lib m dslName of
        Right code -> do
            putStrLn "Code generated successfully!"
            putStrLn "\n--- Generated Code ---"
            T.putStrLn code
            putStrLn "----------------------\n"
            let filename = "generated_circuit" ++ CodeGen.fileExtension CodeGen.defaultTarget
            T.writeFile filename code
            putStrLn $ "Saved to: " ++ filename

        Left err ->
            putStrLn $ "Code generation failed: " ++ err
    return w

event (EventKey (Char 's') Down _ _) w = do
    currentDsl <- readIORef currentDSL
    let nextDsl = case currentDsl of
            "boolean" -> "arith"
            "arith" -> "probcirc"
            "probcirc" -> "boolean"
            _ -> "boolean"
    writeIORef currentDSL nextDsl
    putStrLn $ "Switched to: " ++ nextDsl
    return w

event (EventKey (Char 'p') Down _ _) w = let m = morphism w in do
    let sem = morphToSemantic m
        (inputArity, outputArity) = typeMorph m
    putStrLn "\n=== MORPHISM STRUCTURE ==="
    mapM_ putStrLn (prettySemanticClean sem)
    mapM_ putStrLn (prettySemantic sem)
    return w

event (EventKey (Char 'c') Down _ _) w = let m = morphism w in do
    lib <- readIORef globalCompositeLib
    dslName <- readIORef currentDSL
    let m' = boxIt (lastbox m m)
    let (inAr, outAr) = typeMorph m'
    putStrLn $ "Type: " ++ show inAr ++ " -> " ++ show outAr
    putStrLn "Current morphism will become a new operation."
    putStrLn "Enter operator character (single char): "
    opChar <- getLine
    putStrLn "Enter style string (or press enter for empty): "
    opStyle <- getLine
    dsl <- readIORef currentDSL
    let opName = [head opChar] ++ opStyle
        newLib = defineCompositeOp (head opChar) opStyle m' dsl Map.empty
    modifyIORef globalCompositeLib (Map.union newLib)
    putStrLn $ "Defined composite: " ++ opName
    return w

-- extra 
-- save current proof
event (EventKey (Char 'a') Down _ _) w =
    let m = ifSigR (Sig 'x' (Nothing , "1") 2 2) (Sig 'c' (Nothing , "2") 1 2) (Sig 'd' (Nothing , "2") 1 0) (Sig 'p' (Nothing , "phi") 3 1) (Sig 'f' (Nothing , "") 3 2) in
    return (w {morphism = m , coordinates = initCoor' (worldSize w) m})
-- investigate box
event (EventKey (Char 'i') Down _ _) w = zoomAction w
-- functify 
event (EventKey (Char 'f') Down _ _) w = return (w {morphism = functify (morphism w)})
event (EventKey (Char 'z') Down _ _) w = do {putStrLn (morphTikzerStart (worldMorph w)) ; return w}
event (EventKey (Char 'm') Down _ _) w = let m = testMatch (worldMorph w) in return (w {morphism = m})
event (EventKey (Char 'l') Down _ _) w = 
    let (m , coor) = keepSortMorph (morphism w) (coordinates w) in --coorsortMorph (morphism w) (coordinates w) in 
    let (_ , perm) = knayMorphRem (morphism w) in
        do {print perm ;
            print (applyPerm '-' perm "abcdefghijklmnopqrstuvwxyz") ; 
            return (w {morphism = m , coordinates = coor})}
event (EventKey (Char 't') Down _ _) w =
    let (_ , _ , (p , _) , _ , _) = winfo w in
    let (_ , _ , _ , _ , _ , _ , file) = document w in
    do {writeProof p file ; return w}
event (EventKey (Char 'y') Down _ _) w =
    let (_ , _ , (proof , _) , _ , _) = winfo w in
    let (relat , _ , _ , _ , _ , comment , _) = document w in
    let ext = if null comment || comment == nameRelat relat then "" else "\nnote {" ++ comment ++ "}" in
    do {putStr ext ; putStrLn (saveRelat relat) ; putStr (saveProof proof) ; return w}
event (EventKey (Char 'g') Down _ _) w =
    let m = copyMorph (worldMorph w) in
    let loc = initCoor' 0 m in
        return (w {morphism = copyMorph (worldMorph w) , coordinates = loc})

--event (EventKey (Char 'v') Down _ _) w = do {writePlay "test" (worldMorph w); return w}
-- animation

-- general 
event (EventKey (MouseButton LeftButton) Down _ p) w    =   clickEvent (tM (worldSize w) p) w >>= \v -> event (EventMotion p) v
event (EventKey (MouseButton LeftButton) Up _ _) w      =   return (w {coordinates = deselectNode (coordinates w)})
event (EventKey (MouseButton RightButton) Down _ p) w   =   rightClick w (tM (worldSize w) p)
event (EventKey (SpecialKey KeyTab) Down _ _) w         =   let (goal , _ , hist , moder , name) = winfo w in do
    {   writeFile "tex/test.tex" (allTikz name (relatWrap moder (firstRew (reverse (proofSeq (fst hist)))) (firstRew (reverse (proofSeqM goal))) "x" Axiom) (reverse (proofSeq (fst hist)) ++ tailList (proofSeqM goal)))
        ; return w}
event (EventKey (MouseButton WheelUp) Down _ p) w = wheelUp p w
event (EventKey (MouseButton WheelDown) Down _ p) w = wheelDown p w
event (EventMotion p) w  =
    let (goal , old , hist , moder , name) = winfo w in
    let size = worldSize w in
    let m = morphism w in
    let ori = getOri w in
    let loc = coordinates w in
    let infon = if isPlay w then infoNode (pagePar (document w)) (rePoint size ori (tM size p)) (boxsize size m) m loc moder old else Nothing in
    return (w { coordinates = moveNode (rePoint size ori (tM size p)) loc ,
                winfo = (goal , infon , hist , moder , name) ,
                mouse = tM size p})
event (EventKey (SpecialKey KeySpace) Down _ _) w = autostep2 w
-- type mods 
event (EventKey (MouseButton MiddleButton) Down _ _) w = stampAction (boxsize (worldSize w) (worldMorph w)) w

-- Editor 
event (EventKey (SpecialKey KeyDelete) Down _ _)    w   |   isEdit w    =   return (w { morphism = removeLast (morphism w) ,
                                                                                        coordinates = tailList (coordinates w) })
--event (EventKey (SpecialKey KeyRight) Down _ _)     w   |   isEdit w    =   return (w { morphism = extraWire (morphism w)})
--event (EventKey (SpecialKey KeyLeft) Down _ _)      w   |   isEdit w    =   return (w { morphism = removeWire (morphism w)})
--event (EventKey (SpecialKey KeyUp) Down _ _)        w   |   isEdit w    =   return (w { morphism = upLast (morphism w)})
--event (EventKey (SpecialKey KeyDown) Down _ _)      w   |   isEdit w    =   return (w { morphism = downLast (morphism w)})
-- help
event (EventKey (SpecialKey KeyDown) Down x p) w = event (EventKey (MouseButton WheelDown) Down x p) w
event (EventKey (SpecialKey KeyUp) Down x p) w = event (EventKey (MouseButton WheelUp) Down x p) w
event _ w = return w


interupWorld :: World -> World 
interupWorld w = let (mode , x , ori) = wmode w in w {wmode = (interup mode , x , ori)}

-- ======================
-- The Core step function
-- ======================

step :: Float -> World -> IO World
step _ (Load size p l) = return (Load size p l)
-- Animation: going down the history bar
step _ (World m loc (Anim i True , size , ori) (goal , rew , (hist , hi) , moder , name) mp law ext)
    -- If at end, flip to other side of the relation
    |   i <= 0 && hi <= 0
                    =   --let (p , n , _ , _ , _ , box) = lastProof goal in
                        -- check if relation was proven. If so, flip and skip
                        --if eqMorph m n && lengthProofM goal > 1 then
                        --    let (v1 , v2) = transCoor m box in
                        --    let (w1 , w2) = transCoor box p in
                        --    return (World m loc (Tran 20 v1 v2 box (Tran 20 w1 w2 p (Anim 20 False)) , size , ori) (Just hist , rew , (proofM goal , 1) , reverseMR moder , name) mp law ext)
                        --else
                            return (World m loc (Play , size , ori) (goal , rew , (hist , hi) , moder , name) mp law ext)
--                            Nothing -> return (World m loc (Play , size , ori) (goal , rew , (hist , hi) , moder , name) mp law ext)
    -- If not at end, go to next
    |   i <= 0      =   
--                        let ind = lengthProof hist - 1 - hi in
--                        let (n , box) = proofDown ind hist in
--                        let (v1 , v2) = transCoor m box in
--                        let (w1 , w2) = transCoor box n in
--                        return (World m loc (Tran 30 v1 v2 box (Tran 30 w1 w2 n (Anim 30 True)), size , ori) (goal , rew , (hist , hi - 1) , moder , name) mp law ext)
-- ===========================================================================
                        let ind = lengthProof hist - 1 - hi in
                        let (_ , box) = proofDown ind hist in
                        let (n , loc' , mode) = transitionAnim m box loc (Anim 30 True) in
                        return (World n loc' 
                            (mode , size , ori) (goal , rew , (hist , hi - 1) , moder , name) mp law ext)
    -- Wait for animation to end before next step
    |   otherwise   =   let app = initCoor size m in
                        return (World m (approach (1/ fromIntegral i) loc app) (Anim (i-1) True , size , ori) (goal , rew , (hist , hi) , moder , name) mp law ext)
-- Animation: going up the history bar
step _ (World m loc (Anim i False , size , ori) (goal , rew , (hist , hi) , moder , name) mp law ext)
    -- If at top, stop animation
    |   hi >= (lengthProof hist -1)
                    =   return (World m loc (Play , size , ori) (goal , rew , (hist , hi) , moder , name) mp law ext)
    -- If not at top, go up
    |   i <= 0      =   let ind = lengthProof hist - 2 - hi in
                        let (_ , box) = proofDown ind hist in
                        let (n , loc' , mode) = transitionAnim m (reverseBox box) loc (Anim 30 False) in
                        return (World n loc' 
                            (mode , size , ori) (goal , rew , (hist , hi + 1) , moder , name) mp law ext)
--                        let ind = lengthProof hist - 1 - hi in
--                        let (n , box) = proofUp ind hist in
--                        let (v1 , v2) = transCoor m box in
--                        let (w1 , w2) = transCoor box n in
--                        return (World m loc (Tran 20 v1 v2 box (Tran 20 w1 w2 n (Anim 20 False)), size , ori) (goal , rew , (hist , hi + 1) , moder , name) mp law ext)
    -- Wait for animation to end before next step
    |   otherwise   =   let app = initCoor size m in
                        return (World m (approach (1/ fromIntegral i) loc app) (Anim (i-1) False , size , ori) (goal , rew , (hist , hi) , moder , name) mp law ext)
step _ (World m loc (Tran i app new n t , size , ori) (goal , rew , hist , moder , name) mp law ext)
--    |   i <= 0 && (isPlay' t || isAnim' t)  =   return (gotoHistory n (World n (fmap (\(x , y) -> (size*x , size*y , False)) new) (t , size , ori) (goal , rew , hist , moder , name) mp law ext))
    |   i <= 0                              =   return (World n (fmap (\(x , y) -> (size*x , size*y , False)) new) (t , size , ori) (goal , rew , hist , moder , name) mp law ext)
    |   otherwise   =   return (World m (approach (1/ fromIntegral i) loc
                                (fmap (bimap (size *) (size *)) app)) (Tran (i-1) app new n t , size , ori) (goal , rew , hist , moder , name) mp law ext)
step _ w | isDisp w = return w
step _ w | isPlay w = return (worldStepPlay w)
step _ w | isEdit w = return (worldStepEdit w)
step _ w = return w



-- Start application from loading a file
playLoad :: Bool -> Maybe Int -> IO ()
playLoad full Nothing =
    getScreenSize >>= \t -> let size = if full then sizzle t else sizzle t * 0.9 in
    listInputFiles >>= \s ->
    playIO (setDisplay full size) setColor setSim (Load size (0,0) (mapMaybe stripTxt s)) displayWorld event step
playLoad full (Just i) =
    let size = fromIntegral i in
    listInputFiles >>= \s ->
    playIO (setDisplay full size) setColor setSim (Load size (0,0) (mapMaybe stripTxt s)) displayWorld event step




-- ======================
-- Modifications
-- ======================

approach :: Float -> [(Float , Float , Bool)]  -> [(Float , Float)]  -> [(Float , Float , Bool)]
approach _ [] _ = []
approach _ _ [] = []
approach t ((a , b , False) : l) ((x , y) : r) = (a + (x-a)*t , b + (y-b)*t , False) : approach t l r
approach t ((a , b , True) : l) (_ : r) = (a , b , True) : approach t l r

checkSwapMulti :: [(Int , Bool , Bool , Bool)] -> World -> Maybe World
checkSwapMulti [] _ = Nothing
checkSwapMulti (x : l) w = case checkSwapGen x (morphism w) (coordinates w) of
    Just (wm , wl)  ->  Just (w {morphism = wm , coordinates = wl})
    Nothing         ->  checkSwapMulti l w

checkSwapGen :: (Int , Bool , Bool , Bool) -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
checkSwapGen _ (Start _) _ = Nothing
checkSwapGen _ _ [] = Nothing
checkSwapGen (d , v , w , a) (Op m i o) (x : l)
    |   d <= 0      =   checkSwap v w a (Op m i o) (x : l)
    |   otherwise   =   checkSwapGen (d-1 , v , w , a) m l >>=
            \(wm , wl) -> Just (Op wm i o , x : wl)

checkSwap :: Bool -> Bool -> Bool -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
checkSwap v w a (Op (Op m j q) i o) ((x , y , _) : (x' , y' , _) : r) =
    let (oi , oo) = typeOper o in
    let (qi , qo) = typeOper q in
    if oi == 0 && qo == 0 && i == j then
        if not a then
            Just (Op (Op m (i-qo+qi) o) j q , (x' , y' , v) : (x , y , w) : r)
        else
            Just (Op (Op m i o) (j-oi+oo) q , (x' , y' , v) : (x , y , w) : r)
    else
        if (j + qo) <= i then
            Just (Op (Op m (i-qo+qi) o) j q , (x' , y' , v) : (x , y , w) : r)
        else
            if (i + oi) <= j then
                Just (Op (Op m i o) (j-oi+oo) q , (x' , y' , v) : (x , y , w) : r)
            else
                Nothing
checkSwap _ _ _ _ _ = Nothing

-- Checking whether a node dragged out of place creates a swap. Returns world with swap executed.
worldSwap :: World -> Maybe World
worldSwap w =   worldSwapGen 0 (morphism w) (coordinates w)
                >>= \k -> checkSwapMulti k w

-- Checks whether a node as been dragged out of place, giving options for checking what to swap.
-- Returns: (node index of swap, first node held, second node held, over or under)
worldSwapGen :: Int -> Morph -> [(Float , Float , Bool)] -> Maybe [(Int , Bool , Bool , Bool)]
worldSwapGen q (Op m _ _) ((a , b , k) : (c , d , v) : l)
    |   a < c && (k || v)   =   if k    then    Just [(q , False , True , b < d) , (q+1 , False , False , True)]
                                        else    Just [(q , True , False , b < d) , (q-1 , False , False , True)]
    |   otherwise           =   worldSwapGen (q+1) m ((c , d , v) : l)
worldSwapGen _ _ _ = Nothing


worldMerge :: World -> Float -> Maybe World
worldMerge w bs = worldMerge' bs (mouse w) (morphism w) (coordinates w) >>= \(wm , wl) -> return (w {morphism = wm , coordinates = wl})

worldMerge' :: Float -> Point -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
worldMerge' bs (mx , my) (Op (Op m j p) i o) ((a , b , k) : (c , d , v) : l) =
    let os = (sizeOper o + sizeOper p - 1) in
    if abs (a-c) <= bs*os && abs (b-d) <= bs*os && (k || v) then
        checkMerge (Op (Op m j p) i o) >>= \n -> Just (n , (mx , my, True) : l)
    else
        worldMerge' bs (mx , my) (Op m j p) ((c , d , v) : l)
        >>= \(wm , wl) ->  Just (Op wm i o , (a , b , k) : wl)
worldMerge' _ _ _ _ = Nothing





-- new merger setup



unsafeOp :: Oper -> Bool
unsafeOp (Comp (RS {}) _) = True
unsafeOp _ = False

mergeCoor :: (Float , Float , Bool) -> (Float , Float , Bool) -> (Float , Float , Bool)
mergeCoor (x , y , True) _ = (x , y , True)
mergeCoor _ z = z

tryMerge :: Int -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
tryMerge i (Op (Op m a op) b qp) (x : z : l)
    |   i > 0                       =   tryMerge (i-1) (Op m a op) (z : l) >>= \(m' , l') -> Just (Op m' b qp , x : l')
    |   unsafeOp op || unsafeOp qp  =   Nothing 
    |   otherwise                   =   let (c , mp) = mergeOper (b , qp) (a , op) in
                                        Just (Op m c mp , mergeCoor x z : l)
tryMerge _ _ _           =   Nothing

tryMerger :: Int -> Int -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
tryMerger i j m loc
--    |   i == j          =   Just (m , fmap (\_ -> (0, 0, False)) loc )
    |   i == j          =   Nothing
    |   i + 1 == j      =   tryMerge i m loc
    |   i == j + 1      =   tryMerge j m loc
    |   i < j           =   --case trySwap (j-1) True m loc of 
                            case tryJoinkerRany j (j-1) i m loc of
                                Just (m' , loc')    ->  tryMerger i (j - 1) m' loc'
                                _                   ->  tryJoinkerLany i (i+1) j m loc >>= uncurry (tryMerger (i+1) j)
                                                        --trySwap i True m loc >>= uncurry (tryMerger (i+1) j)
    |   i > j           =   --case trySwap j True m loc of 
                            case tryJoinkerLany j (j+1) i m loc of
                                Just (m' , loc')    ->  tryMerger i (j + 1) m' loc'
                                _                   ->  tryJoinkerRany i (i-1) j m loc >>= uncurry (tryMerger (i-1) j)
                                                        --trySwap (i-1) True m loc >>= uncurry (tryMerger (i-1) j)
    |   otherwise       =   Nothing

tryMergers :: Int -> [Int] -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
tryMergers _ [] _ _ = Nothing
tryMergers i (j : r) m loc = case tryMerger i j m loc of
    Just k      ->  Just k
    Nothing     ->  tryMergers i r m loc



-- check colisio
posCol :: Float -> (Float , Float , Float) -> Morph -> [(Float , Float , Bool)] -> Int -> [Int]
posCol _ _ (Start _) _ _    =   []
posCol _ _ _ [] _           =   []
posCol bs (a , b , h) (Op m _ _) ((c , d , _) : loc) i
                            =   let os = h in --(sizeOper op + h - 1)/2 in 
                                if abs (a-c) <= bs*os && abs (b-d) <= bs*os then
                                i : posCol bs (a , b , h) m loc (i+1) else
                                    posCol bs (a , b , h) m loc (i+1)

posMouse :: Morph -> [(Float , Float , Bool)] -> Int -> Maybe (Int , Float , Float , Float)
posMouse (Start _) _ _  =   Nothing
posMouse _ [] _         =   Nothing
posMouse (Op _ _ op) ((x , y , True) : _) i
                        =   Just (i , x , y , sizeOper op)
posMouse (Op m _ _) ((_ , _ , False) : loc) i
                        =   posMouse m loc (i+1)

mergerCheck :: Float -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
mergerCheck bs m loc    =   posMouse m loc 0 >>=
    \(i , x , y , h)    ->  --Just (m , fmap (\_ -> (x, y, False)) loc )
                            let cols = posCol bs (x , y , h) m loc 0 in
                            tryMergers i cols m loc

posSwap :: Int -> [(Float , Float , Bool)] -> Maybe (Int , Bool)
posSwap i ((x , y , k) : (z , w , v) : l)
    |   (k || v) && x < z   =   Just (i , y < w)
    |   otherwise           =   posSwap (i+1) ((z , w , v) : l)
posSwap _ _ = Nothing

swapperCheck :: Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
swapperCheck m loc = posSwap 0 loc >>= \(i , b) -> trySwap i b m loc

morphVoid :: Morph -> [(Float , Float , Bool)] -> Bool
morphVoid (Op m _ (Comp _ (Start 0))) ((_ , _ , k) : loc) = k || morphVoid m loc
morphVoid (Op m _ _) ((_ , _ , k) : loc) = not k && morphVoid m loc
morphVoid _ _ = False

worldStepPlay :: World -> World
worldStepPlay (Load x y z) = Load x y z
worldStepPlay v =
    let (m , loc) = (morphism v , coordinates v) in
        case swapperCheck m loc of
        Just (m' , loc')    ->  v {morphism = m' , coordinates = loc'}
        Nothing             ->  let bs = boxsize (worldSize v) m in
            case mergerCheck bs m loc of
            Just (m' , loc')    ->  v {morphism = m' , coordinates = loc'}
            Nothing             ->  if morphVoid m loc then
                                        let size = worldSize v in
                                        let (_ , b) = typeMorph m in
                                        let m' = verticleSwitch size b m loc in
                                        let app = initCoor size m'   in
                                        v {morphism = m' , coordinates = approach (1/30) loc app}
                                    else
                                        let app = initCoor (worldSize v) (morphism v)   in
                                        v {coordinates = approach (1/30) (coordinates v) app}

worldStepEdit :: World -> World
worldStepEdit (Load x y z) = Load x y z
worldStepEdit v =
    let (m , loc) = (morphism v , coordinates v) in
    case swapperCheck m loc of
    Just (m' , loc')    ->  v {morphism = m' , coordinates = loc'}
    Nothing             ->  let size = worldSize v in
                            let (_ , b) = typeMorph m in
                            let m' = verticleSwitch size b m loc in
                            let app = initCoor size m'   in
                            v {morphism = m' , coordinates = approach (1/30) loc app}

verticleSwitch :: Float -> Int -> Morph -> [(Float , Float , Bool)] -> Morph
verticleSwitch _    _ (Start a) _ = Start a
verticleSwitch _    _ m [] = m
verticleSwitch size i (Op m j op) ((_ , _ , False) : loc) =
    let (a , b) = typeOper op in
    Op (verticleSwitch size (i-b+a) m loc) j op
verticleSwitch size i (Op m _ op) ((_ , y , True) : _) =
    let (_ , b) = typeOper op in
    let t = i+1-b in
    let r = floor (int2Float t*y/size) in
    Op m r op