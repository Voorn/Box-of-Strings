module World where

-- extended libraries
import Graphics.Gloss

-- project libraries
import Morph
import Display
import Parse
import Theory
import Par


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

-- Different general modes the App can be in
-- Play: Display and manipulate the diagram
-- Tran: Transition into a new morphism
-- Anim: Animation of proof
-- Disp: Display equational theory
data Mode =
    Play
    |   Edit
    |   Tran Int [(Float , Float)] [(Float , Float)] Morph Mode
    |   Anim Int
    |   Disp Int
    deriving Eq

-- The theory datatype: list of operations, schema, equivalence classes and interrelations, and new data coming in
type Theory = ([Sig] , [Schema] , Par Morph , [Phase])

-- Info datatype: telling the current relation displayed and history of rewrites
type Info = (   [Rew] ,                -- Goal information
                [Rew] ,                 -- List of rewrites for highlighted node
                ([Rew] , Int) ,         -- History
                MR ,                    -- Rewrite mode
                String)                 -- Name

-- The State space of the App
data World =
    World
        Morph                       -- Current morphism in workspace, combinatorially 
        [(Float , Float , Bool)]    -- Node information in list: x and y coordinate, and Boolean whether currently being dragged
        (Mode , Float , Orient)     -- Current Mode
        Info                        -- Name
        Point                       -- Mouse position
        Theory                      -- equational theory
    |   Load Float Point [String]

rState :: World -> Morph
rState (World m  _ _ _ _ _) = m
rState (Load {}) = Start 0

-- ==============
-- Initialisation
-- ==============

worldSize :: World -> Float
worldSize (World _  _ (_ , size , _) _ _ _) = size
worldSize (Load size _ _) = size

worldMorph :: World -> Morph
worldMorph (World m _ _ _ _ _) = m
worldMorph (Load {}) = Start 0

worldLoc :: World -> [(Float , Float , Bool)]
worldLoc (World _ l _ _ _ _) = l
worldLoc _ = []

worldInfo :: World -> Info
worldInfo (World _ _ _ info _ _) = info
worldInfo _ = ([] , [] , ([] , 0) , MEqual , "")

worldLaw :: World -> ([Sig] , [Schema] , Par Morph , [Phase])
worldLaw (World _ _ _ _ _ law) = law
worldLaw _ = ([] , [] , [] , [])

setDisplay :: Bool -> Float -> Display
setDisplay full size = if full then FullScreen else InWindow "Box of Strings" (round (size*1.5) , round size) (0 , 0)

setColor :: Color
setColor = white

setSim :: Int
setSim = 60


phaseWorld :: Float -> Orient -> [Sig] -> [Schema] -> Par Morph -> [Phase] -> World
phaseWorld size ori sig hem equiv phase =
    case nextPhase sig hem equiv phase of
        Just (rel , name , sig' , hem' , equiv' , phase')  ->
            let m = startRelat rel in
            let g = goalRelat rel in
            World m [(size/2,size/2,False) | _ <- [2..lengthMorph m]] (Play , size , ori)
                ([RI g] , [] , ([RI m] , 0) , relatMR rel , name) (0 , 0) (sig' , hem' , equiv' , phase')
        Nothing     ->
            World (Start 1) [] (Edit , size , ori) ([RI (Start 1)] , [] , ([RI (Start 1)] , 0) , MLarger , "Editor") (0 , 0) (sig , hem , equiv , [])

-- =========================
-- The core display function
-- =========================

displayStrings :: [String] -> Picture
displayStrings [] = Blank
displayStrings (s : l) = Pictures [Text s , Translate 0 (-180) (displayStrings l)]

displayWorld :: World -> IO Picture
displayWorld (Load size p l) =
    return (Pictures
        (Line [(-(size*3/4) , -(size/2)) , (size*3/4 , -(size/2)) , (size*3/4 , size/2) , (-(size*3/4) , size/2) ,  (-(size*3/4) , -(size/2))] :
        displayMenu ((-size)*2.9/4) (size*3/8) 0 size l (mouseMenu size p)))
displayWorld (World _ _ (Disp v , size , ori) (_ , _ , _ , _ , _) _ (_ , _ , l , _)) = return (displayPar size ori v l)--return (displayEquat v size p l)
displayWorld (World _ _ _ (_ , _ , ([] , _) , _ , _) _ _) = return Blank
displayWorld (World m loc (q , size , ori) (g : goal , info , (hist , hi) , moder , name) (mx , my) (oper , _ , _ , _)) =
    let c | (q /= Play) = grey
          | m == rewMorph g = green
          | insertSort m == insertSort (rewMorph g) = green
          | otherwise = grey in
    return (pictures [
        color ltgrey (Polygon [((-size)/2,size/2) , ((-size)*9/20,size*9/20) , (size*9/20,size*9/20) , (size/2,size/2)]) ,
        color ltgrey (Polygon [((-size)/2,(-size)/2) , ((-size)*9/20,(-size)*9/20) , (size*9/20,(-size)*9/20) , (size/2,(-size)/2)]) ,
        color c (Polygon [((-size)*9/20,(-size)*9/20) , (size*9/20,(-size)*9/20) ,  (size*9/20, size*9/20) , ((-size)*9/20, size*9/20)])  ,
        -- right bar
        pictures (displayRightbar size ori info m) ,
        -- left bar
        if q == Edit then translate ((-size)*3/4) (size/2) (pictures (displayOper size ori oper))
        else translate ((-size)*3/4) (size/2) (displayScrollPosI moder size ori mx my hist hi (g : goal) name),
        Line [((-size)/2,(-size)/2) , ((-size)/2, size/2)] ,
        Line [(size/2,(-size)/2) , (size/2, size/2)]  ,
        translate ((-size)/2) (size/2) (scale 1 (-1) (reOrient size ori (pictures (fst (pictureMorphI size ori m loc)))))
        ])
displayWorld (World {}) = return Blank

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

-- Display scollable relational theory
displayPar :: Float -> Orient -> Int -> Par Morph -> Picture
displayPar size ori i l =
    let (_ , p , loc) = displayPar' size ori 1 0 l [] in
    let per = displayRel size loc loc l in
        Translate (-(size*3/4) + fromIntegral i*size*5/24) (size/6) (Pictures (p ++ per))

displayPar' :: Float -> Orient -> Int -> Int -> Par Morph -> [Int] -> (Int , [Picture] , [Int])
displayPar' _ _ i _ [] v = (i , [] , v)
displayPar' size ori i _ (([] , _) : l) v = displayPar' size ori (i+5) 0 l (v ++ [i+2])
displayPar' size ori i j ((m : r , p) : l) v
    |   j >= 4      =   displayPar' size ori (i+4) 0 ((m : r , p) : l) v
    |   otherwise   =   let (a , b , c) = displayPar' size ori i (j+1) ((r , p) : l) v in
            (a , Translate (size*fromIntegral i/24) (- (size*fromIntegral j/6))
                (scale 1 (-1) (pictures (pictureMorphBoxO True (size/6) ori (0,0) (RI m)))) : b , c)

-- Display a relation
displayRel :: Float -> [Int] -> [Int] -> Par Morph -> [Picture]
displayRel _ _ _ [] = []
displayRel _ [] _ _ = []
displayRel size (i : l) loc ((_ , p) : r) = displayRel' size i loc p ++ displayRel size l loc r

displayRel' :: Float -> Int -> [Int] -> Set Int -> [Picture]
displayRel' _ _ _ [] = []
displayRel' size x1 loc (i : p) =
    let x2 = looku i 0 loc in
    let dx = fromIntegral (abs (x1-x2+2)) in
    let h = dx / (24+dx) in
    let sign = signPre white black (size/128) (if x1 < x2 then RS MLarger (Start 0) else RS MSmaller (Start 0)) in
    let tx = x1+x2 in
        Line [(fromIntegral (x1+1) * size / 24 , 0) ,
        (fromIntegral tx * size / 48 , h * size / 3) ,
        (fromIntegral (x2-1) * size / 24 , 0)]
        : Translate (fromIntegral tx * size / 48) (h * size / 3) sign
        : displayRel' size x1 loc p

displayEquat :: Float -> Float -> Orient -> Point -> Par Morph -> Picture
displayEquat v size ori (mx , my) l =
    let (dx , dy) = ((mx+size/4)/(1.5*size) , my / size) in
    let w = fromIntegral (length l) * size / 4 in
    let h = fromIntegral (maximum (fmap length l)) * size/4 in
    let dh = max 0 (v*h - size) in
    let dw = max 0 (v*w - size*1.5) in
    let tw = -(dw*(dx-0.5)) in
    let th = dh*(dy-0.5) in
        translate tw th (scale v v (pictures (displayEqs size ori l)))


displayEqs :: Float -> Orient -> Par Morph -> [Picture]
displayEqs size ori l = let n = fromIntegral (length l) * size / 4 in displayEqs' size ori (- (n / 2)) l

displayEqs' :: Float -> Orient -> Float -> Par Morph -> [Picture]
displayEqs' _ _ _ [] = []
displayEqs' size ori x ((r , _) : l) = pictures (displayEq size ori x r) : displayEqs' size ori (x+size/4) l

displayEq :: Float -> Orient -> Float -> [Morph] -> [Picture]
displayEq size ori x l = let n = fromIntegral (length l) in
                        Line [(x,size*n/8), (x,(-size)*n/8), (x+size/4,(-size)*n/8), (x+size/4,size*n/8), (x,size*n/8)]
                        : displayEq' size ori x (size*n/8) l

displayEq' :: Float -> Orient -> Float -> Float -> [Morph] -> [Picture]
displayEq' _ _ _ _ [] = []
displayEq' size ori x y (m : l) = Translate x y (scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0,0) (RS MSmaller m))))
    : displayEq' size ori x (y + (-size)/4) l


-- ================
-- File select menu
-- ================


mouseMenu :: Float -> Point -> Int
mouseMenu size (x , y) = let ty = floor (20 * y / size - 1.8) in
    if ty < 0 || ty > 15 then -1 else
        ty + floor (2 * (x + size/4) / size) * 16

selectMenu :: Float -> Int -> [String] -> World -> IO World
selectMenu _ _ [] w = return w
selectMenu size i (a : l) w
    |   i < 0       =   return w
    |   i == 0      =   parseLoc [] a [] [] [] >>= \phase -> return (phaseWorld size LR [] [] [] phase)
    |   otherwise   =   selectMenu size (i-1) l w


displayMenu :: Float -> Float -> Int -> Float -> [String] -> Int -> [Picture]
displayMenu _ _ _ _ [] _ = []
displayMenu x y i size (s : l) p
    |   i < 16 && p == 0    =   Translate x y (scale (size/2500) (size/2500) (Text s)) :
                                Translate (x-1) (y-1) (scale (size/2500) (size/2500) (Text s)) : displayMenu x (y + (-size)/20) (i+1) size l (p-1)
    |   i < 16              =   Translate x y (scale (size/3000) (size/3000) (Text s)) : displayMenu x (y + (-size)/20) (i+1) size l (p-1)
    |   otherwise           =   displayMenu (x + size/2) (y+size*16/20) 0 size (s : l) p

scrollPos :: Float -> Float -> Int -> Float
scrollPos size y n
    |   n <= 2      =   -1
    |   otherwise   =   (fromIntegral n-2) * (y / size) - 1

displayScrollPosI :: MR -> Float -> Orient -> Float -> Float -> [Rew] -> Int -> [Rew] -> String -> Picture
displayScrollPosI moder size ori x y l hi r name = let v = if x <= 0 then scrollPos size y (length l + length r) else fromIntegral (length l) - 2 in
    Translate 0 (v*size/4) (Pictures (
        translate 4 20 (scale (size/4000) (size/4000) (Text name)) :
        translate 5 20 (scale (size/4000) (size/4000) (Text name)) :
        displayScrollPos moder size ori 0 v (reverse l ++ r) (length l - 1 - hi) (length r)))

displayScrollPos :: MR -> Float -> Orient -> Float -> Float -> [Rew] -> Int -> Int -> [Picture]
displayScrollPos moder size _ c _ [] _ n = [translate (size/8) (c + fromIntegral n * size/4) (signPre black white (size/128) (mrRew moder))]
displayScrollPos moder size ori c y (x : l) hi n
    |   y <= -4             =   displayScrollPos moder size ori (c + (-size)/4) (y-1) l (hi-1) n
    |   y >= 1              =   displayScrollPos moder size ori (c + (-size)/4) (y-1) l (hi-1) n
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

displayRightbar :: Float -> Orient -> [Rew] -> Morph -> [Picture]
displayRightbar size _ [] m  = [  translate (size*0.52) (size*6.7/16) (scale (size/2500) (size/2500) (Text "Equations")) ,
                                Line [(size*0.5 , size*0.375) , (size*0.75 , size*0.375)] ,
                                translate (size*0.52) (size*4.7/16) (scale (size/2500) (size/2500)  (Text "Load file")) ,
                                Line [(size*0.5 , size*0.25) , (size*0.75 , size*0.25)] ,
                                Line [(size*0.5 ,(-size)*0.125) , (size*0.75 ,(-size)*0.125)] ,
                                translate (size*0.52) ((-size)*3.3/16) (scale (size/2500) (size/2500) (Text "Flip")) ,
                                Line [(size*0.5 ,(-size)*0.25) , (size*0.75 ,(-size)*0.25)] ,
                                translate (size*0.52) ((-size)*5.3/16) (scale (size/2500) (size/2500) (Text "Autostep")) ,
                                Line [(size*0.5 ,(-size)*0.375) , (size*0.75 ,(-size)*0.375)] ,
                                translate (size*0.52) ((-size)*7.3/16) (scale (size/2500) (size/2500) (Text "Next->")) ,
        Translate (size*0.52) (size*0.22) (scale (size/6000) (size/6000)
                (displayStrings (lines (printMorphI m)))
            )]
displayRightbar size ori info _ =   case displayWheelInfo info of
    Nothing                 ->  []
    Just (m , Nothing)      ->  [translate (size/2) (size/8) (scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0,0) m)))]
    Just (m , Just (x , y , z , w))
                            ->  [translate (size/2) (size/8) (scale 1 (-1) (pictures (pictureMorphBoxO False (size/4) ori (0,0) m))) ,
                                translate (size*33/64) (size*11/32) (scale (7/8) (-(7/8)) (pictures (pictureMorphBoxO False (size/4) ori (0,-0.2) z))) ,
                                translate (size*35/64) (size/2) (scale (5/8) (- (5 / 8)) (pictures (pictureMorphBoxO False (size/4) ori (0,-0.4) w))) ,
                                translate (size*33/64) ((-size)/8) (scale (7/8) (- (7 / 8)) (pictures (pictureMorphBoxO False (size/4) ori (0,0.2) x))) ,
                                translate (size*35/64) ((-size)*11/32) (scale (5/8) (- (5 / 8)) (pictures (pictureMorphBoxO False (size/4) ori (0,0.4) y)))]

-- Adjustment of mouse position
tM :: Float -> Point -> Point
tM size (x , y) = (size/2+x , size/2-y)

-- display Options
displayOper :: Float -> Orient -> [Sig] -> [Picture]
displayOper size ori ((Sig c s i j) : l) =
    [translate (size/32) ((-size)/12) (scale (size/2000) (size/2000) (Text [c])) ,
    translate (size/8) 0 (scale 1 (-1) (pictures (pictureMorphStat (size/8) ori (operMorph (Base (Sig c s i j))))))]
    ++ fmap (translate 0 ((-size)/12)) (displayOper size ori l)
displayOper _ _ _ = []
