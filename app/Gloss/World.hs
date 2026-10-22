module Gloss.World where

-- extended libraries
import Graphics.Gloss
import GHC.Float

-- project libraries
import Morph
import Gloss.Display
import IO.Parse
import Theory.Theory
import Proof
import Semantics.SemanticFree

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

toggleWhy :: Why -> Why
toggleWhy Lemma = Axiom
toggleWhy Axiom = Lemma 
toggleWhy _ = Lemma

toggleMR :: MR -> MR
toggleMR MEqual = MLarger
toggleMR MLarger = MSmaller
toggleMR MSmaller = MEqual

-- Editors move
data Writ =
    Editstart
    |   Editgoal
    |   Editname
    |   Editoper Sig
    deriving Eq

initWrit :: Writ
initWrit = Editstart

extEditoper :: Writ -> Maybe Sig
extEditoper (Editoper s) = Just s
extEditoper _ = Nothing

isEditoper :: Writ -> Bool
isEditoper (Editoper _) = True
isEditoper _ = False

initEdit :: Mode
initEdit = Edit (MEqual , Start 1 , Start 1 , "Name" , Lemma) Editstart

-- Different general modes the App can be in
-- Play: Display and manipulate the diagram
-- Tran: Transition into a new morphism
-- Anim: Animation of proof
-- Disp: Display equational theory
data Mode =
    Play Zoom
    |   Edit Relat Writ
    |   Tran Int [(Float , Float)] [(Float , Float)] Morph Mode (Maybe (Effect , Float)) Zoom
    |   Anim Int Bool
    |   Disp Int Bool
    deriving Eq

interup :: Mode -> Mode
interup (Anim _ _) = Play zoomInit
interup (Tran i l r m x ef zom) = Tran i l r m (interup x) ef zom
interup w = w


semanPrint :: Morph -> [String]
semanPrint m =
    let sem = morphToSemantic m in
    prettySemanticClean sem

---- The theory datatype: list of operations, schema, equivalence classes and interrelations, and new data coming in
--type Theory = ([Sig] , [Schema] , Par Morph , [Phase] , Relat)


-- Info datatype: telling the current relation displayed and history of rewrites
type Info = (   Maybe SprawlProof ,             -- Goal information
                Maybe (Rew , Morph , [Rew] , Float) ,   -- List of rewrites for highlighted node
                (SprawlProof , Int , Float) ,     -- History
                MR ,                -- Rewrite mode
                String)             -- Name

-- special animations and effects for flair
data Effect =
    Popbox Point Float     -- Popbox: box disappearing after being removed
    deriving Eq

type Settings = (FilePath , Bool)

-- String labels, settings, effect, warning bar
type Extra = ((Int, [String]) , Settings , Maybe (Effect , Float) , Maybe (Int , Int) , [String])


-- The State space of the App
data World =
    World
    {   morphism    ::  Morph                       -- Current morphism in workspace, combinatorially 
    ,   coordinates ::  [Coor]    -- Node information in list: x and y coordinate, and Boolean whether currently being dragged
    ,   wmode       ::  (Mode , Float , Orient , Zoom)     -- Current Mode
    ,   winfo       ::  Info                        -- Name
    ,   mouse       ::  Point                       -- Mouse position
    ,   document    ::  Page                        -- Theory history
    ,   extra       ::  Extra
    }
    |   Load Float Point [String] [String] Int (Settings , Orient , Bool)


worldFilePath :: World -> FilePath
worldFilePath (World _ _ _ _ _ _ (_ , (fp , _) , _ , _ , _)) = fp
worldFilePath (Load _ _ _ _ _ ((fp , _) , _ , _)) = fp

isEdit' :: Mode -> Bool
isEdit' (Edit {}) = True
isEdit' _ = False


rState :: World -> Morph
rState (World m  _ _ _ _ _ _) = m
rState (Load {}) = Start 0

-- mode checkers 
isPlay' :: Mode -> Bool
isPlay' (Play _) = True
isPlay' _ = False

isAnim' :: Mode -> Bool
isAnim' (Anim _ _) = True
isAnim' _ = False

isPlay :: World -> Bool
isPlay (Load {}) = False
isPlay w = case wmode w of
    (Play _ , _ , _ , _)  ->  True
    _               ->  False

isEdit :: World -> Bool
isEdit (Load {}) = False
isEdit w = case wmode w of
    (Edit {} , _ , _ , _)  ->  True
    _               ->  False

isTran :: World -> Bool
isTran (Load {}) = False
isTran w = case wmode w of
    (Tran {} , _ , _ , _)  ->  True
    _               ->  False

isAnim :: World -> Bool
isAnim (Load {}) = False
isAnim w = case wmode w of
    (Anim _ _ , _ , _ , _)  ->  True
    _               ->  False

isDisp :: World -> Bool
isDisp (Load {}) = False
isDisp w = case wmode w of
    (Disp _ _ , _ , _ , _)  ->  True
    _               ->  False

setMode :: Mode -> World -> World
setMode _ (Load a f b c d fp)  =   Load a f b c d fp
setMode mode w          =   let (_ , y , z , zom) = wmode w in w {wmode = (mode , y , z , zom)}

getDisp :: World -> (Int , Bool)
getDisp w = case wmode w of
    (Disp v b , _ , _ , _)    ->  (v , b)
    (Anim v b , _ , _ , _)  ->  (v , b)
    _                   ->  (0 , True)

getOri :: World -> Orient
getOri (Load {}) = LR
getOri w = let (_ , _ , ori , _) = wmode w in ori

-- ==========
-- Zoomin
-- ==========

-- Zoom information
-- Point (x , y): top left corner of zoom box. Coordinates are proportional to 1, not size
-- Float z: proportional size of zoombox. So bottom-right corner is (x+z, y+z)
-- Bool: expresses whether zooming is allowed
type Zoom = (Point , Float , Bool)

zoomInit :: Zoom
zoomInit = ((0 , 0) , 1 , True)

zoomFalse :: Zoom
zoomFalse = ((0 , 0) , 1 , False)

zoomSet :: Bool -> Zoom
zoomSet b = ((0 , 0) , 1 ,b)

zoomReset :: Zoom -> Zoom
zoomReset (_ , _ , b) = ((0 , 0) , 1 , b)

worldZoom :: World -> Zoom
worldZoom (World _ _ (_ , _ , _ , zom) _ _ _ _) = zom
worldZoom _ = zoomInit

zoomPic :: Float -> Zoom -> Orient -> Picture -> Picture
zoomPic size ((x , y) , z , _) ori pic = 
    let (a , b) = (- (x*size) , - y*size) in 
    Scale (1/z) (1/z) (Translate a b  pic)

zoomPic' :: Float -> Zoom -> Orient -> Picture -> Picture
zoomPic' size zom ori pic = Translate ((-size)/2) (size/2) (zoomPic size zom ori (Translate (size/2) ((-size)/2) pic))

zoomIn :: Zoom -> Point -> Float -> Zoom
zoomIn ((x , y) , z , b) (mx , my) size = let fac = z/20 in ((x + mx*fac/size , y + my*fac/size) , z-fac , b)

zoomOut :: Zoom -> Point -> Zoom
zoomOut ((x , y) , z , b) (mx , my) =
    let z' = (z*20/19) in
        if z' >= 1 then ((0 , 0) , 1 , b)
        else
    let fac = (1-z')/(1-z) in
    ((x*fac , y*fac) , z' , b)

zoomPoint :: Float -> Zoom -> Point -> Point
zoomPoint size ((x , y) , z , True) (mx , my) = (x*size + mx*z , y*size + my*z)
zoomPoint _ _ mp = mp

zoomEffect :: Float -> Zoom -> Effect -> Effect
zoomEffect size ((x , y) , z , True) (Popbox (px , py) ps) = Popbox ((px - x*size)/z , (py-y*size)/z) (ps/z)
zoomEffect _ _ ef = ef

zoomMove :: Point -> Float -> Zoom -> Zoom
zoomMove (mx , my) size ((x , y) , z , b)
    |   z >= 1   =   ((0 , 0) , 1 , b)
    |   z < 1 && mx >= 0 && mx <= size && my >= 0 && my <= size      =
            let x'
                  | mx < size*0.05 = max 0 (x-z/100)
                  | mx > size*0.95 = min (1-z) (x+z/100)
                  | otherwise = x in
            
            let y'
                  | my < size*0.05 = max 0 (y-z/100)
                  | my > size*0.95 = min (1-z) (y+z/100)
                  | otherwise = y in
            ((x' , y') , z , b)
    |   otherwise   =   ((x , y) , z , b)

zoomApproach :: Zoom -> Zoom -> Zoom
zoomApproach ((x , y) , z , True) ((x' , y') , z' , _) = ((x*0.95+x'*0.05 , y*0.95+y'*0.05) , z*0.95 + z'*0.05 , True)
zoomApproach zom _ = zom

zoomFocus :: Point -> Float -> Zoom
zoomFocus (x , y) r = ((max 0 (min (1-r) (x-r/2)) , max 0 (min (1-r) (y-r/2))) , r , True)

zoomOutTran :: Morph -> [(Float , Float)] -> Mode -> Mode
zoomOutTran m loc md = Tran 30 loc loc m md Nothing zoomInit

gotoZoom :: Mode -> Zoom
gotoZoom (Play zom) = zom
gotoZoom _ = zoomInit

-- ==============
-- Initialisation
-- ==============

worldSize :: World -> Float
worldSize (Load size _ _ _ _ _) = size
worldSize w = let (_ , s , _ , _) = wmode w in s

worldMorph :: World -> Morph
worldMorph (World m _ _ _ _ _ _) = m
worldMorph (Load {}) = Start 0

worldLoc :: World -> [Coor]
worldLoc (Load {}) = []
worldLoc w = coordinates w

worldInfo :: World -> Info
worldInfo (World _ _ _ info _ _ _) = info
worldInfo _ = (Nothing , Nothing , ((Start 0 , Spra []) , 0 , 0) , MEqual , "")

worldPage :: World -> Page
worldPage (World _ _ _ _ _ law _) = law
worldPage _ = ((MEqual , Start 1 , Start 1 , "" , Axiom) , Nothing , ([] , [] , [] , []) , [] , Initi "" "" , [] , "" , "void")

worldOrient :: World -> Orient
worldOrient (World _ _ (_ , _ , ori , _) _ _ _ _) = ori
worldOrient _ = LR

defaultExtra :: Extra
defaultExtra = ((0 , []) , ("input/" , True) , Nothing , Nothing , [])

worldExtra :: World -> Extra
worldExtra (World _ _ _ _ _ _ extr) = extr
worldExtra _ = defaultExtra

worldMode :: World -> Mode
worldMode w = let (mode , _ , _ , _) = wmode w in mode

updateMouse :: Point -> World -> World
updateMouse p w = w {mouse = tM (worldSize w) p}

setDisplay :: Bool -> Float -> Display
setDisplay full size = if full then FullScreen else InWindow "Box of Strings" (round (size*1.5) , round size) (0 , 0)

setColor :: Color
setColor = white

setColorB :: Color
setColorB = black

setSim :: Int
setSim = 60

-- Adjustment of mouse position
tM :: Float -> Point -> Point
tM size (x , y) = (size/2+x , size/2-y)

