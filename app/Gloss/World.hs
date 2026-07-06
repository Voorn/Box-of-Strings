module Gloss.World where

-- extended libraries
import Graphics.Gloss
import GHC.Float

-- project libraries
import Morph
import Gloss.Display
import Parse
import Theory
import Par2
import Proof 
import SemanticFree

-- ====================
-- GLOSS CORE FUNCTIONS
-- ====================

-- Utility functions


sizzle :: (Int , Int) -> Float
sizzle (x , y) = min (fromIntegral y) (fromIntegral x / 1.5)

til :: [a] -> [a]
til [] = []
til (_ : l) = l

looku :: Int -> a -> [a] -> a
looku _ m [] = m
looku i m (a : l)
    |   i <= 0      =   a
    |   otherwise   =   looku (i-1) m l

remov :: Int -> [a] -> [a]
remov _ [] = []
remov i (a : l)
    |   i <= 0      =   l
    |   otherwise   =   a : remov (i-1) l



-- ==========
-- Data types
-- ==========

data Wtyp =
    WDef 
    |   WLem
    deriving Eq

wtypWhy :: Wtyp -> Why 
wtypWhy WDef = Axiom 
wtypWhy WLem = Lemma

toggleWtyp :: Wtyp -> Wtyp 
toggleWtyp WDef = WLem 
toggleWtyp WLem = WDef 

data Writ =
    WRel Wtyp (Maybe Morph)
    |   WOpe Char (Maybe Int) Writ
    deriving Eq

initWrit :: Writ 
initWrit = WRel WDef Nothing


-- Different general modes the App can be in
-- Play: Display and manipulate the diagram
-- Tran: Transition into a new morphism
-- Anim: Animation of proof
-- Disp: Display equational theory
data Mode =
    Play
    |   Edit Writ
    |   Tran Int [(Float , Float)] [(Float , Float)] Morph Mode
    |   Anim Int Bool
    |   Disp Int
    deriving Eq

interup :: Mode -> Mode
interup (Anim _ _) = Play
interup (Tran i l r m x) = Tran i l r m (interup x) 
interup w = w


semanPrint :: Morph -> [String] 
semanPrint m = 
    let sem = morphToSemantic m in
    (prettySemanticClean sem)

---- The theory datatype: list of operations, schema, equivalence classes and interrelations, and new data coming in
--type Theory = ([Sig] , [Schema] , Par Morph , [Phase] , Relat)


-- Info datatype: telling the current relation displayed and history of rewrites
type Info = (   Maybe Proof ,             -- Goal information
                Maybe (Rew , Morph , [Rew]) ,   -- List of rewrites for highlighted node
                (Proof , Int) ,     -- History
                MR ,                -- Rewrite mode
                String)             -- Name

type Extra = (Int, [String])

-- The State space of the App
data World =
    World
    {   morphism    ::  Morph                       -- Current morphism in workspace, combinatorially 
    ,   coordinates ::  [(Float , Float , Bool)]    -- Node information in list: x and y coordinate, and Boolean whether currently being dragged
    ,   wmode       ::  (Mode , Float , Orient)     -- Current Mode
    ,   winfo       ::  Info                        -- Name
    ,   mouse       ::  Point                       -- Mouse position
    ,   document    ::  Page                        -- Theory history
    ,   extra       ::  Extra
    }
    |   Load Float Point [String]

isEdit' :: Mode -> Bool 
isEdit' (Edit _) = True 
isEdit' _ = False


rState :: World -> Morph
rState (World m  _ _ _ _ _ _) = m
rState (Load {}) = Start 0

-- mode checkers 
isPlay' :: Mode -> Bool 
isPlay' Play = True
isPlay' _ = False

isAnim' :: Mode -> Bool 
isAnim' (Anim _ _) = True
isAnim' _ = False

isPlay :: World -> Bool 
isPlay (Load {}) = False 
isPlay w = case wmode w of 
    (Play , _ , _)  ->  True 
    _               ->  False

isEdit :: World -> Bool 
isEdit (Load {}) = False 
isEdit w = case wmode w of 
    (Edit _ , _ , _)  ->  True 
    _               ->  False

isTran :: World -> Bool 
isTran (Load {}) = False 
isTran w = case wmode w of 
    (Tran {} , _ , _)  ->  True 
    _               ->  False

isAnim :: World -> Bool 
isAnim (Load {}) = False 
isAnim w = case wmode w of 
    (Anim _ _ , _ , _)  ->  True 
    _               ->  False

isDisp :: World -> Bool 
isDisp (Load {}) = False 
isDisp w = case wmode w of 
    (Disp _ , _ , _)  ->  True 
    _               ->  False

setMode :: Mode -> World -> World 
setMode _ (Load a b c)  =   Load a b c
setMode mode w          =   let (_ , y , z) = wmode w in w {wmode = (mode , y , z)}

getDisp :: World -> Int 
getDisp w = case wmode w of 
    (Disp v , _ , _)    ->  v 
    (Anim v _ , _ , _)  ->  v 
    _                   ->  0

getOri :: World -> Orient
getOri (Load {}) = LR 
getOri w = let (_ , _ , ori) = wmode w in ori

-- ==============
-- Initialisation
-- ==============

worldSize :: World -> Float
worldSize (Load size _ _) = size
worldSize w = let (_ , s , _) = wmode w in s

worldMorph :: World -> Morph
worldMorph (World m _ _ _ _ _ _) = m
worldMorph (Load {}) = Start 0

worldLoc :: World -> [(Float , Float , Bool)]
worldLoc (Load _ _ _) = []
worldLoc w = coordinates w

worldInfo :: World -> Info
worldInfo (World _ _ _ info _ _ _) = info
worldInfo _ = (Nothing , Nothing , ((Start 0 , []) , 0) , MEqual , "")

worldPage :: World -> Page
worldPage (World _ _ _ _ _ law _) = law
worldPage _ = ((MEqual , Start 1 , Start 1 , "" , Axiom) , Nothing , ([] , [] , [] , []) , [] , [] , "" , "void")

worldOrient :: World -> Orient
worldOrient (World _ _ (_ , _ , ori) _ _ _ _) = ori
worldOrient _ = LR

worldExtra :: World -> Extra 
worldExtra (World _ _ _ _ _ _ extr) = extr
worldExtra _ = (0 , [])

worldMode :: World -> Mode 
worldMode w = let (mode , _ , _) = wmode w in mode

updateMouse :: Point -> World -> World 
updateMouse p w = w {mouse = tM (worldSize w) p}

setDisplay :: Bool -> Float -> Display
setDisplay full size = if full then FullScreen else InWindow "Box of Strings" (round (size*1.5) , round size) (0 , 0)

setColor :: Color
setColor = white

setSim :: Int
setSim = 60


pageWorld :: Float -> Orient -> Page -> Extra -> World
pageWorld size ori (rel , viv , theory , future , past , comment , file) ext
    |   isEnd rel   =   World (Start 1) [] (Edit initWrit , size , ori) (Nothing , Nothing , ((Start 1 , []) , 0) , MLarger , "Editor" ) (0 , 0) ((MEqual , Start 1 , Start 1 , "Editor" , Axiom) , Nothing , theory , future , past , comment , file) ext
    |   otherwise   =
        let m = startRelat rel in
        let g = goalRelat rel in
        let name = nameRelat rel in
        case viv of 
            Nothing ->  let goal = if m == g then Nothing else Just (g , []) in
                        let hist = (m , []) in 
                World m [(size/2,size/2,False) | _ <- [2..lengthMorph m]] (Play , size , ori)
                        (goal , Nothing , (hist , 0) , relatMR rel , name) (0 , 0) (rel , viv , theory , future , past , comment , file) ext
            Just (n , i , hist , goal) -> 
                World n [(size/2,size/2,False) | _ <- [2..lengthMorph n]] (Play , size , ori)
                        (goal , Nothing , (hist , i) , relatMR rel , name) (0 , 0) (rel , viv , theory , future , past , comment , file) ext

-- =========================
-- The core display function
-- =========================

displayStrings :: Float -> [String] -> [Picture]
displayStrings _ [] = []
displayStrings i (s : l) = Translate 0 i (Text s) : displayStrings (i-180) l

goalColor :: Mode ->  Morph -> Maybe Proof -> Color
goalColor Play m (Just goal)
    | m == goalProof goal = green
    | eqMorph m (goalProof goal) = green
    | otherwise = grey
goalColor _ _ _ = grey

ziploc :: [(Point , Int , Int)] -> [String] -> [(Point , String)]
ziploc [] _ = []
ziploc _ [] = []
ziploc ((p , _ , _) : l) (s : r) = (p , s) : ziploc l r

displayWorld :: World -> IO Picture
displayWorld (Load size p l) =
    return (Pictures
        (Line [(-(size*3/4) , -(size/2)) , (size*3/4 , -(size/2)) , (size*3/4 , size/2) , (-(size*3/4) , size/2) ,  (-(size*3/4) , -(size/2))] :
        displayMenu ((-size)*2.9/4) (size*7/16) 0 size l (mouseMenu size p)))
displayWorld (World _ _ (Disp v , size , ori) (_ , _ , _ , _ , _) _ (_ , _ , (_ , s , l , _) , _ , _ , _ , _) _) = return (displayTheory size ori v (l ++ exampleSchemas s))
displayWorld (World m loc (q , size , ori) (goal , info , (hist , hi) , moder , name) (mx , my) ((_ , _ , _ , _ , why) , _ , (oper , _ , _ , _) , _ , _ , comment , _) ext) =
    let (_ , points) = pictureMorphI size ori m loc in 
    let sem = [] in --ziploc points ["a" | _ <- [0..100]] in 
    let c = goalColor q m goal in
    let rightBar = displayRightbar (isEdit' q) size ori info m ext in
    return (pictures ([
--        color ltgrey (Polygon [((-size)/2,size/2) , ((-size)*9/20,size*9/20) , (size*9/20,size*9/20) , (size/2,size/2)]) ,
--        color ltgrey (Polygon [((-size)/2,(-size)/2) , ((-size)*9/20,(-size)*9/20) , (size*9/20,(-size)*9/20) , (size/2,(-size)/2)]) ,
        color c (Polygon [((-size)*9/20,(-size)*9/20) , (size*9/20,(-size)*9/20) ,  (size*9/20, size*9/20) , ((-size)*9/20, size*9/20)])  ,
        -- right bar
        pictures rightBar ,
        -- left bar
        case q of 
            Edit writ  ->  Pictures (editDisplay size ori oper writ)
            _          ->  translate ((-size)*3/4) (size*3/8) (displayScrollPosI moder why size ori mx my hist hi goal name)
        ,
        Line [((-size)/2,(-size)/2) , ((-size)/2, size/2)] ,
        Line [(size/2,(-size)/2) , (size/2, size/2)]  ,
        translate ((-size)/2) (size/2) (scale 1 (-1) (reOrient size ori (pictures (fst (pictureMorphI size ori m loc)))))]
        ++ displayInfo size ((-size)*((32-2*stringSplitSkip 135 comment)/64)) (stringSplit 135 comment)
        ++ if isEdit' q then [] else [translate (x-size/2) (-y+size/2) (Text s) | ((x , y) , s) <- sem]
        ))
--displayWorld (World {}) = return Blank

editDisplay :: Float -> Orient -> [Sig] -> Writ -> [Picture]
editDisplay size ori oper (WRel WDef Nothing) = 
    [Translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text "Make Definition Start")) ,
    Translate (size/2) (size/6) (scale (size/4000) (size/4000) (Text "Make Definition")) ,
    Translate (size/2+1) (size/6) (scale (size/4000) (size/4000) (Text "Make Definition")) ,
    Translate (size/2) (size/8) (scale (size/4000) (size/4000) (Text "Make Lemma")) ,
    translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper))]
editDisplay size ori oper (WRel WDef (Just n)) = 
    [Translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text "Make Definition Goal")) ,
    Translate (size/2) (size/6) (scale (size/4000) (size/4000) (Text "Make Definition")) ,
    Translate (size/2+1) (size/6) (scale (size/4000) (size/4000) (Text "Make Definition")) ,
    Translate (size/2) (size/8) (scale (size/4000) (size/4000) (Text "Make Lemma")) ,
    translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper)) ,
    translate (size/2) (size/8) (scale 1 (-1) (pictures (pictureMorphStat (size/4) ori n))) ]
editDisplay size ori oper (WRel WLem Nothing) = 
    [Translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text "Make Lemma Start")) ,
    Translate (size/2) (size/6) (scale (size/4000) (size/4000) (Text "Make Definition")) ,
    Translate (size/2) (size/8) (scale (size/4000) (size/4000) (Text "Make Lemma")) ,
    Translate (size/2+1) (size/8) (scale (size/4000) (size/4000) (Text "Make Lemma")) ,
    translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper))]
editDisplay size ori oper (WRel WLem (Just n)) = 
    [Translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text "Make Lemma Goal")) ,
    Translate (size/2) (size/6) (scale (size/4000) (size/4000) (Text "Make Definition")) ,
    Translate (size/2) (size/8) (scale (size/4000) (size/4000) (Text "Make Lemma")) ,
    Translate (size/2+1) (size/8) (scale (size/4000) (size/4000) (Text "Make Lemma")) ,
    translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper)) , 
    translate (size/2) (size/8) (scale 1 (-1) (pictures (pictureMorphStat (size/4) ori n))) ]
editDisplay size ori oper (WOpe d Nothing _) = 
    [Translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text (d : " : ? -> ?"))) , translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper))]
editDisplay size ori oper (WOpe d (Just a) _) = 
    [Translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text (d : " : " ++ show a ++ " -> ?"))) , translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper))]


displayInfo :: Float -> Float -> [String] -> [Picture]
displayInfo _ _ [] = []
displayInfo size y (s : l) = 
    color black (translate ((-size)*31/64) (y+1)   (scale (size/5000) (size/5000) (Text s))) :
    translate ((-size)*31/64)   y       (scale (size/5000) (size/5000) (Text s)) :
    displayInfo size (y + ((-size)/32)) l

-- Display utility functions

-- Display a scrollable history
displayScroll :: Float -> Orient -> Float -> [Rew] -> [Picture]
displayScroll _ _ _ [] = []
displayScroll size ori x (m : l) =  scale 1 (-1) (pictures (pictureMorphBoxO True (x * size/4) ori (0,0) m))
    : fmap (translate (x/8*size/4) ((-x)*size/4)) (displayScroll size ori (x*3/4) l)

displayScroll2 :: Float -> Orient -> [Rew] -> [Picture]
displayScroll2 _ _ [] = []
displayScroll2 size ori (m : l) =  scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0,0) m))
    : fmap (translate 0 ((-size)/4)) (displayScroll2 size ori l)

-- ===========
-- Theory Page
-- ===========

displayTheory :: Float -> Orient -> Int -> [Relat] -> Picture
displayTheory size ori i l =
    let (_ , p) = displayTheory' size ori 1 0 l in
        Translate (-(size*3/4) + fromIntegral i*size*5/20) (size/2.25) (Pictures p)
--displayRelat :: Float -> Orient -> Int -> Relat -> Picture

displayTheory' :: Float -> Orient -> Int -> Int -> [Relat] -> (Int , [Picture])
displayTheory' _ _ i _ [] = (i , [])
displayTheory' size ori i j ((x , m , n , s , w) : l)
--    |   m > n       =   displayTheory' size ori i j l
    |   j <= 5      =   let (k , p) = displayTheory' size ori i (j+5) l in
                        (k ,
                        Translate (size*fromIntegral i/20) (20 - (size*fromIntegral j/10)) (scale 0.15 0.15 (Text (uptoBar s)))
                        : Translate (size*fromIntegral i/20) (- (size*fromIntegral j/10)) (scale 1 (-1) (pictures (pictureMorphBoxO True (size/5) ori (0,0) (RI m))))
                        : Translate (size*fromIntegral i/20) (- (size*fromIntegral (j+2)/10)) (scale 1 (-1) (pictures (pictureMorphBoxO True (size/5) ori (0,0) (RS x n "" w))))
                        : p)
    |   otherwise   =   displayTheory' size ori (i+5) 0 ((x , m , n , s , w) : l)



-- ================
-- File select menu
-- ================


iconFlip :: Picture 
iconFlip = Color dkgrey (Pictures [
    Polygon [(-7,7) , (-7,6) , (6,-7) , (7,-7) , (7,-6) , (-6,7) ] ,
    Polygon [(6,6) , (6,1) , (5,4) , (2,2) , (4,5) , (1,6) ] ,
    Polygon [(-6,-6) , (-6,-1) , (-5,-4) , (-1,-1) , (-4,-5) , (-1,-6) ]
    ])

iconZoom :: Picture 
iconZoom = Color dkgrey (Pictures [
    Polygon [(-7,-7) , (-7,7) , (7,7) , (7,-7) , (-7,-7) , (-6,-6) , (6,-6) , (6,6) , (-6,6) , (-6,-6)  ] ,
    Polygon [(5,5) , (5,0) , (4,3) , (1,1) , (3,4) , (0,5) ] ,
    Polygon [(-5,-5) , (-5,0) , (-4,-3) , (-1,-1) , (-3,-4) , (0,-5) ] ,
    Polygon [(5,-5) , (5,0) , (4,-3) , (1,-1) , (3,-4) , (0,-5) ] ,
    Polygon [(-5,5) , (-5,0) , (-4,3) , (-1,1) , (-3,4) , (0,5) ]
    ])

mouseMenu :: Float -> Point -> Int
mouseMenu size (x , y) = let ty = floor (32 * y / size - 1.3) in
    if ty < 0 || ty > 29 then -1 else
        ty + floor (3 * (x + size/4) / size) * 30

selectMenu :: Bool -> Float -> Int -> [String] -> World -> IO World
selectMenu _ _ _ [] w = return w
selectMenu b size i (a : l) w
    |   i < 0       =   return w
    |   i == 0      =   initPage b a >>= \page -> return (pageWorld size LR page (0 , []))
    |   otherwise   =   selectMenu b size (i-1) l w


displayMenu :: Float -> Float -> Int -> Float -> [String] -> Int -> [Picture]
displayMenu _ _ _ _ [] _ = []
displayMenu x y i size (s : l) p
    |   i < 30 && p == 0    =   Translate x y (scale (size/4000) (size/4000) (Text s)) :
                                Translate (x-1) (y) (scale (size/4000) (size/4000) (Text s)) : displayMenu x (y + (-size)/32) (i+1) size l (p-1)
    |   i < 30              =   Translate x y (scale (size/5000) (size/5000) (Text s)) : displayMenu x (y + (-size)/32) (i+1) size l (p-1)
    |   otherwise           =   displayMenu (x + size/3) (y+size*30/32) 0 size (s : l) p

scrollPos :: Float -> Float -> Int -> Float
scrollPos size y n
    |   n <= 2      =   -1
    |   otherwise   =   (fromIntegral n-2) * (y / size) - 1

displayScrollPosI :: MR -> Why -> Float -> Orient -> Float -> Float -> Proof -> Int -> Maybe Proof -> String -> Picture
displayScrollPosI moder why size ori x y l hi r name = 
    --let v = if x <= 0 then scrollPos size y (length l + length r) else fromIntegral (length l - 2 - hi) in --fromIntegral (length l) - 2 in
    let v = fromIntegral (lengthProof l - 2 - hi) in
        Translate 0 (v*size/4) (Pictures (
            --(if v == -1 && length l > 1 then translate 0 (size/6) (scale (size/2000) (size/2000) (Text "Animate")) else Blank) :
            translate 4 (20 + size/24) (scale (size/2000) (size/2000) (Text (show why))) :
            translate 5 (20 + size/24) (scale (size/2000) (size/2000) (Text (show why))) :
            translate 4 20 (scale (size/5000) (size/5000) (Text name)) :
            translate 4 21 (scale (size/5000) (size/5000) (Text name)) :
            displayScrollPos moder size ori 0 v (reverse (proofSeq l) ++ proofSeqM r) (lengthProof l  - 1 - hi) (lengthProofM r )))

displayScrollPos :: MR -> Float -> Orient -> Float -> Float -> [Rew] -> Int -> Int -> [Picture]
displayScrollPos moder size _ c _ [] _ n = 
                                let y = (c + fromIntegral n * size/4) in
                                [
                                color black (Polygon [(0 , y+size/200) , (0 , y-(size/200)) , (size/4 , y-(size/200)) , (size/4 , y+size/200)]) ,
                                translate (size/8) y (signPre black white (size/128) (mrRew moder))
                                ]
displayScrollPos moder size ori c y (x : l) hi n
    |   y <= -4             =   displayScrollPos moder size ori (c + (-size)/4) (y-1) l (hi-1) n
    |   y >= 2              =   displayScrollPos moder size ori (c + (-size)/4) (y-1) l (hi-1) n
    |   hi == 0             =   color dkgrey (translate 0 c (Polygon [(0 ,0) , (0 ,(-size)/4) , (size/4 ,(-size)/4) , (size/4 ,0) , (0 ,0)]))
                                : translate 0 c (scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0,0) x)))
                                : displayScrollPos moder size ori (c + (-size)/4) (y-1) l (hi-1) n
    |   otherwise           =   translate 0 c (scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0,0) x))) : displayScrollPos moder size ori (c + (-size)/4) (y-1) l (hi-1) n

scrollSelect :: Float -> Float -> Int -> Int
scrollSelect size y n =   min (n-1) (max (-1) (floor (fromIntegral (n+2) * y / size - 1)))

-- utility
two :: a -> [a] -> (a , a)
two m [] = (m , m)
two m [a] = (a , m)
two _ (a : b : _) = (a , b)


-- =====================
-- The wheel of rewrites
-- =====================

displayWheelInfo :: [Rew] -> Maybe (Rew , Maybe (Rew , Rew , Rew , Rew))
displayWheelInfo [] = Nothing
displayWheelInfo [m] = Just (m , Nothing)
displayWheelInfo (m : a : l) =
    let (x , y) = two m (a : l) in
    let (z , w) = two m (reverse (a : l)) in
        Just (m , Just (x , y , z , w))

displayRightbar :: Bool -> Float -> Orient -> Maybe (Rew , Morph , [Rew]) -> Morph -> Extra -> [Picture]
displayRightbar b size ori Nothing m ext = 
    --let (iconFlip) = ext in
                [   -- icons
                    translate (size*11/16) ((-size)*9/32) (scale (size / 256) (size / 256) iconFlip) ,
                    translate (size*9/16) ((-size)*5/32) (scale (size / 256) (size / 256) iconZoom) ,
                    translate (size*0.52) (size*6.7/16) (scale (size/2500) (size/2500) (Text "Equations")) ,
                    Line [(size*0.5 , size*0.375) , (size*0.75 , size*0.375)] ,
                    translate (size*0.52) (size*4.7/16) (scale (size/2500) (size/2500)  (Text "Load file")) ,
                    Line [(size*0.5 , size*0.25) , (size*0.75 , size*0.25)] ,
                    Line [(size*0.5 ,(-size)*0.125) , (size*0.75 ,(-size)*0.125)] ,
                    translate (size*0.52) ((-size)*3.7/16) (scale (size/4000) (size/4000) (Text "Zoom")) ,
                    translate (size*0.64) ((-size)*2.9/16) (scale (size/4000) (size/4000) (Text "Add")) ,
                    translate (size*0.64) ((-size)*3.7/16) (scale (size/4000) (size/4000) (Text "Rel")) ,
                    translate (size*0.64) ((-size)*5.7/16) (scale (size/4000) (size/4000) (Text ("Ori:" ++ show ori))) ,
                    Line [(size*0.5 ,(-size)*0.25) , (size*0.75 ,(-size)*0.25)] ,
                    translate (size*0.51) ((-size)*4.9/16) (scale (size/4000) (size/4000) (Text "Auto-")) ,
                    translate (size*0.51) ((-size)*5.7/16) (scale (size/4000) (size/4000) (Text "Reduce")) ,
                    Line [(size*0.5 ,(-size)*0.375) , (size*0.75 ,(-size)*0.375)] ,
                    translate (size*0.64) ((-size)*7/16) (scale (size/4000) (size/4000) (Text "Next")) ,
                    translate (size*0.64) ((-size)*7.5/16) (scale (size/4000) (size/4000) (Text "-->")) ,
                    Line [(size*0.625 ,(-size)*0.125) , (size*0.625 ,(-size)*0.5)] ,
                    translate (size*0.52) ((-size)*7/16) (scale (size/4000) (size/4000) (Text "Back")) ,
                    translate (size*0.52) ((-size)*7.5/16) (scale (size/4000) (size/4000) (Text "<--"))
            ]
                    ++ if b then [] else 
                    let stri = lines (printMorphI m) in
                    let v = 9 / int2Float (max 9 (length stri)) in
                    [translate (size*0.51) (size*0.21) (scale (v*size/5000) (v*size/5000)
                    (Pictures (displayStrings 0 stri))) ,
                    translate (size*0.51) (size*0.21+1) (scale (v*size/5000) (v*size/5000)
                    (Pictures (displayStrings 0 stri)))
                    ]
displayRightbar _ size ori (Just (_ , _ , info)) _ _ =   case displayWheelInfo info of
    Nothing                 ->  []
    Just (m , Nothing)      ->  [translate (size/2) (size/8) (scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0,0) m)))]
    Just (m , Just (x , y , z , w))
                            -> [translate (size/2) (size/8) (scale 1 (-1) (pictures (pictureMorphBoxO False (size/4) ori (0,0) m))) ,
                                translate (size*33/64) (size*11/32) (scale (7/8) (-(7/8)) (pictures (pictureMorphBoxO False (size/4) ori (0,-0.2) z))) ,
                                translate (size*35/64) (size/2) (scale (5/8) (- (5 / 8)) (pictures (pictureMorphBoxO False (size/4) ori (0,-0.4) w))) ,
                                translate (size*33/64) ((-size)/8) (scale (7/8) (- (7 / 8)) (pictures (pictureMorphBoxO False (size/4) ori (0,0.2) x))) ,
                                translate (size*35/64) ((-size)*11/32) (scale (5/8) (- (5 / 8)) (pictures (pictureMorphBoxO False (size/4) ori (0,0.4) y)))]

-- Adjustment of mouse position
tM :: Float -> Point -> Point
tM size (x , y) = (size/2+x , size/2-y)


-- display Options
displayOper :: Bool -> Float -> Orient -> Float -> [Sig] -> [Picture]
displayOper b size ori y ((Sig c s i j) : l) =
    let xt = if b then (size/11) else (size/7) in
    [translate (size/32) (y + (-size)/16) (scale (size/3000) (size/3000) (Text [c])) ,
    translate xt (y - size/80) (scale 1 (-1) (reOrient (size/12) ori (pictures (pictureMorphStat (size/12) ori (operMorph (Base (Sig c s i j))))))) ]
    --(pictures (pictureMorphStat (size/12) ori (operMorph (Base (Sig c s i j))))))]
    ++ (displayOper (not b) size ori (y + (-size)/20) l)
displayOper _ _ _ _ _ = []
