module Gloss.Event where

-- standard library
import Data.Maybe
import Data.Bifunctor

import GHC.Float
-- extended libraries
import Graphics.Gloss
import Graphics.Gloss.Interface.IO.Interact
import Graphics.Gloss.Interface.Environment
--import Graphics.Gloss.Export
import System.Exit

import Control.Concurrent

-- project libraries
import Morph
import Theory.Rewrite
import Gloss.Display
import Gloss.Actions
import IO.Parse
import Gloss.World
import Theory.HyperMatch
import Theory.Theory
import Proof
import IO.Write

-- semantic addition
import Semantics.SemanticFree
--import DSL.ProbCircDSL as ProbCirc
--import SemanticInterpreterPoly as Poly
import Semantics.Evaluation
import qualified Semantics.Equivalence as Equiv
import qualified Semantics.CodeGen
import Semantics.SemanticFree (prettySemanticClean)
import DSL.ProbCircDSL (printProb)
import Semantics.CodeGen

import qualified Data.Text.IO as T
import Data.IORef
import qualified Data.Map as Map
import System.IO.Unsafe (unsafePerformIO)

{-# NOINLINE globalCompositeLib #-}
globalCompositeLib :: IORef CompositeLibrary
globalCompositeLib = unsafePerformIO (newIORef Map.empty)
{-# NOINLINE currentDSL #-}
currentDSL :: IORef String
currentDSL = unsafePerformIO (newIORef "probcirc")
-- currentDSL = unsafePerformIO (newIORef "boolean")

optionsKey :: Char -> Int
optionsKey 'r' = 0
optionsKey 'o' = 1
optionsKey 'a' = 2
optionsKey 'z' = 3
optionsKey '3' = 4
optionsKey '4' = 5
optionsKey '5' = 6
optionsKey '6' = 7
optionsKey '7' = 8
optionsKey '<' = 9
optionsKey '>' = 10
optionsKey _ = -1

optionsKeys :: String
optionsKeys = sortSet "roaz<>"

-- ===============
-- Event structure
-- ===============

event :: Event -> World -> IO World
event (EventKey (SpecialKey KeyEsc) Down _ _) _ = exitSuccess

-- zoom 
event (EventKey (MouseButton WheelDown) Down _ p) (Load size _ f l i fp) = return (Load (size-10) (tM (size-10) p) f l i fp)
event (EventKey (MouseButton WheelUp) Down _ p) (Load size _ f l i fp) = return (Load (size+10) (tM (size+10) p) f l i fp)

-- loading file 
event (EventKey (MouseButton LeftButton) Down _ p) (Load size _ f l i fp) =
    selectMenu False (mouseMenu size (tM size p)) (menupop i l) (Load size (tM size p) f l i fp)
event (EventKey (MouseButton RightButton) Down _ p) (Load size _ f l i fp) =
    selectMenu True (mouseMenu size (tM size p)) (menupop i l) (Load size (tM size p) f l i fp)
event (EventKey (SpecialKey KeyLeft) Down _ p) (Load size _ f l i fp) =   return (Load size (tM size p) f l (max 0 (i-1)) fp)
event (EventKey (SpecialKey KeyRight) Down _ p) (Load size _ f l i fp) =   return (Load size (tM size p) f l (i+1) fp)
event (EventMotion p) (Load size _ f l i fp) = return (Load size (tM size p) f l i fp)
event _ (Load size p f l i fp) = return (Load size p f l i fp)

-- when transitioning, don't do anything
event (EventKey (MouseButton LeftButton) Down _ _) w     |   isTran w    =   return (interupWorld w)
event (EventKey (MouseButton LeftButton) Down _ _) w     |   isAnim w    =   return (interupWorld w)
event (EventMotion p) w     |   isTran w    =   return (updateMouse p w)
event (EventMotion p) w     |   isAnim w    =   return (updateMouse p w)
event _ w                   |   isTran w    =   return w
event _ w                   |   isAnim w    =   return w
-- when displaying
event (EventKey (MouseButton LeftButton) Down _ _) w    |   isDisp w    =   return (setMode (Play zoomInit) w)
event (EventKey (MouseButton WheelUp) Down _ _) w       |   isDisp w    =   let (t , b) = getDisp w in return (setMode (Disp (t+1) b) w)
event (EventKey (MouseButton WheelDown) Down _ _) w     |   isDisp w    =   let (t , b) = getDisp w in return (setMode (Disp (t-1) b) w)
event (EventKey (MouseButton RightButton) Down _ _) w   |   isDisp w    =   let (t , b) = getDisp w in return (setMode (Disp t (not b)) w)
event (EventMotion p) w                                 |   isDisp w    =   return (updateMouse p w)
event _ w                                               |   isDisp w    =   return w
-- editor
event (EventKey (Char c) Down (Modifiers _ _ ct) _) w   |   isEdit w    =
    let (q , _ , _ , _) = wmode w in 
        editorAddChar [c] ct w q
-- semantics
event (EventKey (Char c) Down _ _) w 
    |   inSet c "ceghpqsw" = semEvent c w 
    --do {printProb (worldMorph w) ; return w}
-- functify 
event (EventKey (SpecialKey KeyLeft) Down _ _) w =   doOption 9 w
event (EventKey (SpecialKey KeyRight) Down _ _) w =   doOption 10 w
event (EventKey (Char 'f') Down _ _) w = 
    do {
        return w
    }
event (EventKey (Char 'i') Down _ _) w = do {putStrLn (morphTikzerStart (worldMorph w)) ; return w}
event (EventKey (Char 'm') Down _ _) w = let m = testMatch (worldMorph w) in return (w {morphism = m})
event (EventKey (Char 't') Down _ _) w =
    let (_ , _ , (p , _ , _) , _ , _) = winfo w in
    let (_ , _ , _ , _ , _ , _ , _ , file) = document w in
    do {writeProof (sprawlProofTrace p) file ; return w}
event (EventKey (Char 'y') Down _ _) w =
    let (_ , _ , (proof , _ , _) , _ , _) = winfo w in
    let (relat , _ , _ , _ , _ , _ , comment , _) = document w in
    let ext = if null comment || comment == nameRelat relat then "" else "\nnote {" ++ comment ++ "}" in
    do {putStr ext ; putStrLn (saveRelat relat) ; putStr (saveProof (sprawlProofTrace proof)) ; return w}
event (EventKey (Char 'k') Down _ _) w@(World m _ _ _ _ page _) =
    let (file , tex) = reconstPage page "" in
    do {
        putStrLn ("\n============\n" ++ file ++ "\n============\n" ++ tex) ;
        return w
    }
event (EventKey (Char c) Down _ _) w
    |   inSet c optionsKeys     =   doOption (optionsKey c) w
    |   otherwise               =   return w

--event (EventKey (Char 'v') Down _ _) w = do {writePlay "test" (worldMorph w); return w}
-- animation

-- general 
event (EventKey (MouseButton LeftButton) Down _ p) w    =   clickEvent (tM (worldSize w) p) w >>= \v -> event (EventMotion p) v
event (EventKey (MouseButton LeftButton) Up _ _) w      =   return (w {coordinates = deselectNode (coordinates w)})
event (EventKey (MouseButton RightButton) Down _ p) w   =   rightClick w (tM (worldSize w) p)
--event (EventKey (SpecialKey KeyTab) Down _ _) w         =   let (goal , _ , (hist , hi , hf) , moder , name) = winfo w in do
--    {   writeFile "tex/test.tex" (allTikz name (relatWrap moder (firstRew (reverse (proofSeq (sprawlProofTrace hist)))) (firstRew (reverse (proofSeqM goal))) "x" Axiom) (reverse (proofSeq (fst3 hist)) ++ tailList (proofSeqM goal)))
--        ; return w}
event (EventKey (MouseButton WheelUp) Down _ p) w = wheelUp p w
event (EventKey (MouseButton WheelDown) Down _ p) w = wheelDown p w
event (EventMotion p) w  =
    let (goal , old , hist , moder , name) = winfo w in
    let size = worldSize w in
    let m = morphism w in
    let ori = getOri w in
    let loc = coordinates w in
    let p' = zoomPoint size (worldZoom w) (rePoint size ori (tM size p)) in
    let infon = if isPlay w then infoNode (pagePar (document w)) p' (boxsize size m) m loc moder old 0 else Nothing in
    return (w { coordinates = moveNode p' loc ,
                winfo = (goal , infon , hist , moder , name) ,
                mouse = tM size p})
event (EventKey (SpecialKey KeySpace) Down _ _) w = autostep2 w
-- type mods 
event (EventKey (MouseButton MiddleButton) Down _ _) w = stampActionF (boxsize (worldSize w) (worldMorph w)) w

-- Editor 
event (EventKey (SpecialKey KeyDelete) Down _ _)    w   |   isEdit w    =   editBackspace w
--event (EventKey (SpecialKey KeyRight) Down _ _)     w   |   isEdit w    =   return (w { morphism = extraWire (morphism w)})
--event (EventKey (SpecialKey KeyLeft) Down _ _)      w   |   isEdit w    =   return (w { morphism = removeWire (morphism w)})
--event (EventKey (SpecialKey KeyUp) Down _ _)        w   |   isEdit w    =   return (w { morphism = upLast (morphism w)})
--event (EventKey (SpecialKey KeyDown) Down _ _)      w   |   isEdit w    =   return (w { morphism = downLast (morphism w)})
-- help
event (EventKey (SpecialKey KeyDown) Down x p) w = event (EventKey (MouseButton WheelDown) Down x p) w
event (EventKey (SpecialKey KeyUp) Down x p) w = event (EventKey (MouseButton WheelUp) Down x p) w
event _ w = return w


emptyLines :: [String] -> [String]
emptyLines [] = []
emptyLines ("" : l) = emptyLines l
emptyLines (c : l) = c : emptyLines l

fst3 :: (a , b , c) -> a
fst3 (a , _ , _) = a

interupWorld :: World -> World
interupWorld w = let (mode , x , ori , zom) = wmode w in w {wmode = (interup mode , x , ori , zom)}

stripString :: String -> [String]
stripString "" = []
stripString ('\n' : l) = [] : stripString l
stripString (c : l) = appString c (stripString l)

appString :: Char -> [String] -> [String]
appString c [] = [[c]]
appString c (l : rest) = (c : l) : rest

--displayStrings :: Float -> [String] -> [Picture]
--displayStrings _ [] = []
--displayStrings y (s : l) = translate 0 y (Text s) : displayStrings (y - 32) l

-- ======================
-- The Core step function
-- ======================
effectSound :: Settings -> Maybe (Effect , Float) -> Float -> IO ()
effectSound _ Nothing _ = return ()
effectSound set (Just (Popbox p _ , _)) size = do {_ <- playpop set p size ; return ()}


step :: Float -> World -> IO World
step _ (Load size p f l i fp) = return (Load size p f l i fp)
-- Animation: going down the history bar
step _ (World m loc (Anim i True , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) mp law ext)
    -- If at end, flip to other side of the relation
    |   i <= 0 && hi >= (sprawlProofLength hist - 1)
                    =   return (World m loc (Play zoomInit , size , ori , zoomInit) (goal , rewstep rew , (hist , hi , f/2) , moder , name) mp law (stepExtra ext))
    -- If not at end, go to next
    |   i <= 0      =   let (_ , _ , _ , _ , box) = sprawlNext trivPrStep (snd hist) hi in
                        let (n , loc' , mode) = transitionAnim size m box loc (Anim 30 True) in
                        return (World n loc'
                            (mode , size , ori , zom) (goal , rewstep rew , (hist , hi + 1 , 1) , moder , name) mp law (stepExtra ext))
    -- Wait for animation to end before next step
    |   otherwise   =   let app = initCoor size m in
                        return (World m (approach (1/ fromIntegral i) loc app) (Anim (i-1) True , size , ori , zom) (goal , rew , (hist , hi , f/2) , moder , name) mp law (stepExtra ext))
-- Animation: going up the history bar
step _ (World m loc (Anim i False , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) mp law ext)
    -- If at top, stop animation
    |   i <= 0 && hi <= 0
                    =   return (World m loc ((Play zoomInit) , size , ori , zom) (goal , rewstep rew , (hist , hi , f/2) , moder , name) mp law (stepExtra ext))
    -- If not at top, go up
    |   i <= 0      =   let (_ , _ , _ , _ , box) = sprawlNext trivPrStep (snd hist) (hi-1) in
                        let (n , loc' , mode) = transitionAnim size m (reverseBox box) loc (Anim 30 False) in
                        return (World n loc'
                            (mode , size , ori , zom) (goal , rewstep rew , (hist , hi - 1 , -1) , moder , name) mp law (stepExtra ext))
    -- Wait for animation to end before next step
    |   otherwise   =   let app = initCoor size m in
                        return (World m (approach (1/ fromIntegral i) loc app) (Anim (i-1) False , size , ori , zom) (goal , rewstep rew , (hist , hi , f/2) , moder , name) mp law (stepExtra ext))
step _ (World m loc (Tran i app new n t ef azom , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) mp law (a , b , c , d , e))
    |   i <= 0      =   let scal = sizeMorph'' n / sizeMorph'' m in
                        do
                            effectSound b ef size ;
                            return (World n (endtranCoor scal size n new) (t , size , ori , zom)
                                    (goal , rewstep rew , (hist , hi , f/2) , moder , name) mp law (a , b , ef , d , e))
    |   otherwise   =   return (World m (approach (1/ fromIntegral i) loc
                                (fmap (bimap (size *) (size *)) app)) (Tran (i-1) app new n t ef azom , size , ori , zoomApproach zom azom)
                                (goal , rewstep rew , (hist , hi , f/2) , moder , name) mp law (stepExtra (a , b , c , d , e)))
step _ w | isDisp w = return w
step _ w | isPlay w = return (worldStepPlay w)
step _ w@(World _ _ (q@(Edit {}) , _ , _ , _) _ _ _ _) = return (worldStepEdit w q)
step _ w = return w

endtranCoor :: Float -> Float -> Morph -> [Point] -> [Coor]
endtranCoor _ _ _ [] = []
endtranCoor _ _ (Start _) _ = []
endtranCoor scal size (Op m _ (Comp _ _)) ((x , y) : l) = (size*x , size*y , False , 0) : endtranCoor scal size m l
endtranCoor scal size (Op m _ _) ((x , y) : l)  = (size*x , size*y , False , scal) : endtranCoor scal size m l

rewstep :: Maybe (Rew, Morph, [Rew], Float) -> Maybe (Rew, Morph, [Rew], Float)
rewstep Nothing = Nothing
rewstep (Just (a , b , c , f)) = Just (a , b , c , f/2)

screenz :: Bool -> Maybe Int -> IO Float
screenz _ (Just i) = return (fromIntegral i)
screenz full Nothing = getScreenSize >>= \t -> return (if full then sizzle t else sizzle t * 0.9)






-- ======================
-- Modifications
-- ======================

approach :: Float -> [Coor]  -> [(Float , Float)]  -> [Coor]
approach _ [] _ = []
approach _ _ [] = []
approach t ((a , b , False , abf) : l) ((x , y) : r) = (a + (x-a)*t , b + (y-b)*t , False , 0.1+abf*0.9) : approach t l r
approach t ((a , b , True , abf) : l) (_ : r) = (a , b , True , 0.1+abf*0.9) : approach t l r

checkSwapMulti :: [(Int , Bool , Bool , Bool)] -> World -> Maybe World
checkSwapMulti [] _ = Nothing
checkSwapMulti (x : l) w = case checkSwapGen x (morphism w) (coordinates w) of
    Just (wm , wl)  ->  Just (w {morphism = wm , coordinates = wl})
    Nothing         ->  checkSwapMulti l w

checkSwapGen :: (Int , Bool , Bool , Bool) -> Morph -> [Coor] -> Maybe (Morph , [Coor])
checkSwapGen _ (Start _) _ = Nothing
checkSwapGen _ _ [] = Nothing
checkSwapGen (d , v , w , a) (Op m i o) (x : l)
    |   d <= 0      =   checkSwap v w a (Op m i o) (x : l)
    |   otherwise   =   checkSwapGen (d-1 , v , w , a) m l >>=
            \(wm , wl) -> Just (Op wm i o , x : wl)

checkSwap :: Bool -> Bool -> Bool -> Morph -> [Coor] -> Maybe (Morph , [Coor])
checkSwap v w a (Op (Op m j q) i o) ((x , y , _ , f) : (x' , y' , _ , f') : r) =
    let (oi , oo) = typeOper o in
    let (qi , qo) = typeOper q in
    if oi == 0 && qo == 0 && i == j then
        if not a then
            Just (Op (Op m (i-qo+qi) o) j q , (x' , y' , v , f') : (x , y , w , f) : r)
        else
            Just (Op (Op m i o) (j-oi+oo) q , (x' , y' , v , f') : (x , y , w , f) : r)
    else
        if (j + qo) <= i then
            Just (Op (Op m (i-qo+qi) o) j q , (x' , y' , v , f') : (x , y , w , f) : r)
        else
            if (i + oi) <= j then
                Just (Op (Op m i o) (j-oi+oo) q , (x' , y' , v , f') : (x , y , w , f) : r)
            else
                Nothing
checkSwap _ _ _ _ _ = Nothing

-- Checking whether a node dragged out of place creates a swap. Returns world with swap executed.
worldSwap :: World -> Maybe World
worldSwap w =   worldSwapGen 0 (morphism w) (coordinates w)
                >>= \k -> checkSwapMulti k w

-- Checks whether a node as been dragged out of place, giving options for checking what to swap.
-- Returns: (node index of swap, first node held, second node held, over or under)
worldSwapGen :: Int -> Morph -> [Coor] -> Maybe [(Int , Bool , Bool , Bool)]
worldSwapGen q (Op m _ _) ((a , b , k , _) : (c , d , v , cdf) : l)
    |   a < c && (k || v)   =   if k    then    Just [(q , False , True , b < d) , (q+1 , False , False , True)]
                                        else    Just [(q , True , False , b < d) , (q-1 , False , False , True)]
    |   otherwise           =   worldSwapGen (q+1) m ((c , d , v , cdf) : l)
worldSwapGen _ _ _ = Nothing


worldMerge :: World -> Float -> Maybe World
worldMerge w bs = worldMerge' bs (mouse w) (morphism w) (coordinates w) >>= \(wm , wl) -> return (w {morphism = wm , coordinates = wl})

worldMerge' :: Float -> Point -> Morph -> [Coor] -> Maybe (Morph , [Coor])
worldMerge' bs (mx , my) (Op (Op m j p) i o) ((a , b , k , abf) : (c , d , v , cdf) : l) =
    let os = (sizeOper o + sizeOper p - 1) in
    if abs (a-c) <= bs*os && abs (b-d) <= bs*os && (k || v) then
        checkMerge (Op (Op m j p) i o) >>= \n -> Just (n , (mx , my, True , 1) : l)
    else
        worldMerge' bs (mx , my) (Op m j p) ((c , d , v , cdf) : l)
        >>= \(wm , wl) ->  Just (Op wm i o , (a , b , k , abf) : wl)
worldMerge' _ _ _ _ = Nothing





-- new merger setup



unsafeOp :: Oper -> Bool
unsafeOp (Comp (RS {}) _) = True
unsafeOp _ = False

-- size of operations, taking zero for non-box
sizeBoper :: Oper -> Float
sizeBoper (Comp r m) = sizeOper (Comp r m)
sizeBoper _ = 1

mergeCoor :: Oper -> Oper -> Oper -> Coor -> Coor -> Coor
mergeCoor qp op mp (x , y , True , f) (_ , _ , _ , f') =   (x , y , True , max (f * sizeBoper qp) (f' * sizeBoper op) / sizeOper mp)
mergeCoor qp op mp (_ , _ , _ , f) (x , y , z , f') = (x , y , z , max (f * sizeBoper qp) (f' * sizeBoper op) / sizeOper mp)

tryMerge :: Int -> Morph -> [Coor] -> Maybe (Morph , [Coor])
tryMerge i (Op (Op m a op) b qp) (x : z : l)
    |   i > 0                       =   tryMerge (i-1) (Op m a op) (z : l) >>= \(m' , l') -> Just (Op m' b qp , x : l')
    |   unsafeOp op || unsafeOp qp  =   Nothing
    |   otherwise                   =   let (c , mp) = mergeOper (b , qp) (a , op) in
                                        Just (Op m c mp , mergeCoor qp op mp x z : l)
tryMerge _ _ _           =   Nothing

tryMerger :: Int -> Int -> Morph -> [Coor] -> Maybe (Morph , [Coor])
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

tryMergers :: Int -> [Int] -> Morph -> [Coor] -> Maybe (Morph , [Coor])
tryMergers _ [] _ _ = Nothing
tryMergers i (j : r) m loc = case tryMerger i j m loc of
    Just k      ->  Just k
    Nothing     ->  tryMergers i r m loc



-- check colisio
posCol :: Float -> (Float , Float , Float) -> Morph -> [Coor] -> Int -> [Int]
posCol _ _ (Start _) _ _    =   []
posCol _ _ _ [] _           =   []
posCol bs (a , b , h) (Op m _ _) ((c , d , _ , _) : loc) i
                            =   let os = h in --(sizeOper op + h - 1)/2 in 
                                if abs (a-c) <= bs*os && abs (b-d) <= bs*os then
                                i : posCol bs (a , b , h) m loc (i+1) else
                                    posCol bs (a , b , h) m loc (i+1)

posMouse :: Morph -> [Coor] -> Int -> Maybe (Int , Float , Float , Float)
posMouse (Start _) _ _  =   Nothing
posMouse _ [] _         =   Nothing
posMouse (Op _ _ op) ((x , y , True , _) : _) i
                        =   Just (i , x , y , sizeOper op)
posMouse (Op m _ _) ((_ , _ , False , _) : loc) i
                        =   posMouse m loc (i+1)

mergerCheck :: Float -> Float -> Morph -> [Coor] -> Maybe (Morph , [Coor])
mergerCheck size bs m loc    =  let (_ , b) = typeMorph m in
                                let n = (if morphVoid m loc then verticleSwitch size b m loc else m) in
    posMouse n loc 0 >>=
    \(i , x , y , h)    ->  let cols = posCol bs (x , y , h) n loc 0 in
                            tryMergers i cols n loc

posSwap :: Int -> [Coor] -> Maybe (Int , Bool)
posSwap i ((x , y , k , _) : (z , w , v , zwf) : l)
    |   (k || v) && x < z   =   Just (i , y < w)
    |   otherwise           =   posSwap (i+1) ((z , w , v , zwf) : l)
posSwap _ _ = Nothing

swapperCheck :: Morph -> [Coor] -> Maybe (Morph , [Coor])
swapperCheck m loc = posSwap 0 loc >>= \(i , b) -> trySwap i b m loc

morphVoid :: Morph -> [Coor] -> Bool
morphVoid (Op m _ (Comp _ (Start 0))) ((_ , _ , k , _) : loc) = k || morphVoid m loc
morphVoid (Op m _ _) ((_ , _ , k , _) : loc) = not k && morphVoid m loc
morphVoid _ _ = False

stepExtra :: Extra -> Extra
stepExtra (a , b , Nothing , d , k) = (a , b , Nothing , fmap (\(x , y) -> (max 0 (x-1) , y)) d , k)
stepExtra (a , b , Just (e , i) , d , k)
    |   i <= 0      =   (a , b , Nothing , fmap (\(x , y) -> (max 0 (x-1) , y)) d , k)
    |   otherwise   =   (a , b , Just (e , i-0.05) , fmap (\(x , y) -> (max 0 (x-1) , y)) d , k)

worldStepPlay :: World -> World
worldStepPlay (Load x y f z i fp) = Load x y f z i fp
worldStepPlay v =
    let size = worldSize v in
    let (m , loc) = (morphism v , coordinates v) in
    let (mx , my) = mouse v in
    let ext = stepExtra (extra v) in
    let (mp , rew , (pp , pip , pf) , mr , s) = winfo v in
    let win = (mp , rewstep rew , (pp , pip , pf/2) , mr , s) in
    let (wmo , wa , wp , wzom) = wmode v in
    let ori = worldOrient v in
    let gozom = zoomMove (rePoint size ori (mx , my)) size (gotoZoom wmo) in
    let wmod = (Play gozom, wa , wp , zoomApproach (zoomMove (rePoint size ori (mx , my)) size wzom) gozom) in
        case swapperCheck m loc of
        Just (m' , loc')    ->  let scal = sizeMorph'' m' / sizeMorph'' m in
                                v {morphism = m' , coordinates = scaleCoor scal loc' , wmode = wmod , extra = ext}
        Nothing             ->  let bs = boxsize (worldSize v) m in
            case mergerCheck size bs m loc of
            Just (m' , loc')    ->  let scal = sizeMorph'' m' / sizeMorph'' m in
                                    v {morphism = m' , coordinates = scaleCoor scal loc' , wmode = wmod , extra = ext}
            Nothing             ->  if morphVoid m loc then
                                        let (_ , b) = typeMorph m in
                                        let m' = verticleSwitch size b m loc in
                                        let app = initCoor size m'   in
                                        v {morphism = m' , coordinates = approach (1/30) loc app , winfo = win , wmode = wmod , extra = ext}
                                    else
                                        let app = initCoor (worldSize v) (morphism v) in
                                        --let app =   if coorHold (coordinates v) 
                                        --            then initCoorFilter (worldSize v) (morphism v) mx my zoom 
                                        --            else initCoor (worldSize v) (morphism v) in
                                        v {coordinates = approach (1/30) (coordinates v) app , winfo = win , wmode = wmod , extra = ext}

-- Step
worldStepEdit :: World -> Mode -> World
worldStepEdit w (Edit _ (Editoper s))=
    let n = operMorph (Base s) in
    w {morphism = n , coordinates = initCoor' (worldSize w) n}
worldStepEdit w q@(Edit (mr , st , go , nam , why) writ)=
    let (m , loc) = (morphism w , coordinates w) in
    let (_ , size , ori , zom) = wmode w in
    case swapperCheck m loc of
    Just (m' , loc')    ->  w {morphism = m' , coordinates = loc'}
    Nothing             ->  let (_ , b) = typeMorph m in
                            let (m' , loc') = horSwitch m loc in
                            let m'' = verticleSwitch size b m' loc' in
                            let app = initCoor size m''   in
                            let mode'
                                  | writ == Editstart = Edit (mr , m , go , nam , why) Editstart
                                  | writ == Editgoal = Edit (mr , st , m , nam , why) Editgoal
                                  | otherwise = q in
                            w {morphism = m'' , coordinates = approach (1/30) loc' app , wmode = (mode' , size , ori , zom)}
worldStepEdit w _ = w


verticleSwitch :: Float -> Int -> Morph -> [Coor] -> Morph
verticleSwitch _    _ (Start a) _ = Start a
verticleSwitch _    _ m [] = m
verticleSwitch size i (Op m j op) ((_ , _ , False , _) : loc) =
    let (a , b) = typeOper op in
    Op (verticleSwitch size (i-b+a) m loc) j op
verticleSwitch size i (Op m _ op) ((_ , y , True , _) : _) =
    let (_ , b) = typeOper op in
    let t = i+1-b in
    let r = min (i-b) (floor (int2Float t*y/size)) in
    Op m r op

horSwitch :: Morph -> [Coor] -> (Morph , [Coor])
horSwitch (Start a) co = (Start a , co)
horSwitch (Op (Start a) i o) co = (Op (Start a) i o , co)
horSwitch m [] = (m , [])
horSwitch m [xy] = (m , [xy])
horSwitch (Op (Op m i o) j q) ((qx , qy , qk , qg) : (ox , oy , ok , og) : loc)
    |   qk && qx < ox       =   let (qi , qo) = typeOper q in
                                let n = Op (Op m 0 q) (max 0 (i-qi+qo)) o in
                                if typecheckMorph n
                                then (n , (ox , oy , ok , og) : (qx , qy , qk , qg) : loc)
                                else (Op (Op m i o) j q , (qx , qy , qk , qg) : (ox , oy , ok , og) : loc)
    |   ok && qx < ox       =   let (oi , oo) = typeOper o in
                                let n = Op (Op m (max 0 (j-oo+oi)) q) 0 o in
                                if typecheckMorph n
                                then (n , (ox , oy , ok , og) : (qx , qy , qk , qg) : loc)
                                else (Op (Op m i o) j q , (qx , qy , qk , qg) : (ox , oy , ok , og) : loc)
    |   otherwise           =   let (m' , loc') = horSwitch (Op m i o) ((ox , oy , ok , og) : loc) in
                                (Op m' j q , (qx , qy , qk , qg) : loc')


-- semantic events

-- eqwhspcg

semEvent :: Char -> World -> IO World
semEvent 'e' w = 
    let m = morphism w in do
    dslName <- readIORef currentDSL
    lib <- readIORef globalCompositeLib
    case parseMode dslName of
        Just mode -> evaluateWithMode mode lib m
        Nothing -> putStrLn $ "Unknown DSL: " ++ dslName
    return w
semEvent 'q' w@(World _ _ _ _ _ page _) = do
    dslName <- readIORef currentDSL
    lib <- readIORef globalCompositeLib
    result <- Equiv.validateCurrentPage dslName lib page
    return w
semEvent 'w' w@(World _ _ _ _ _ page _) = do
    dslName <- readIORef currentDSL
    lib <- readIORef globalCompositeLib
    Equiv.validateTheoryFromPage dslName lib page
    return w
semEvent 'h' w@(World m _ _ _ _ page _) = do
    dslName <- readIORef currentDSL
    lib <- readIORef globalCompositeLib
    case generateFromMorph lib m dslName of
        Right code -> do
            putStrLn "Code generated successfully!"
            putStrLn "\n--- Generated Code ---"
            T.putStrLn code
            putStrLn "----------------------\n"
            let filename = "generated_circuit" ++ fileExtension defaultTarget
            T.writeFile filename code
            putStrLn $ "Saved to: " ++ filename
        Left err ->
            putStrLn $ "Code generation failed: " ++ err
    return w
semEvent 's' w = do
    currentDsl <- readIORef currentDSL
    let nextDsl = case currentDsl of
            "boolean" -> "arith"
            "arith" -> "probcirc"
            "probcirc" -> "boolean"
            _ -> "boolean"
    writeIORef currentDSL nextDsl
    putStrLn $ "Switched to: " ++ nextDsl
    return w
semEvent 'p' w = let m = morphism w in do
    let sem = morphToSemantic m
        (inputArity, outputArity) = typeMorph m
    putStrLn "\n=== MORPHISM STRUCTURE ==="
    mapM_ putStrLn (prettySemanticClean sem)
    mapM_ putStrLn (prettySemantic sem)
    return w
semEvent 'c' w = let m = morphism w in do
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
semEvent 'g' w = 
    let m = morphism w in 
    let (a , b , c , d , _) = extra w in    do
    dslName <- readIORef currentDSL
    lib <- readIORef globalCompositeLib
    let str = (case evaluateProb lib m TruthTable Nothing of 
            Right result -> prettyResult result 
            _ -> "") in do --evaluateWithMode mode lib m
        putStrLn str ;
        return w {extra = (a , b , c , d , emptyLines (stripString str))}
