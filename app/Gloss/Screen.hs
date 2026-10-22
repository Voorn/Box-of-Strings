module Gloss.Screen where

-- extended libraries
import Graphics.Gloss
import GHC.Float
import Sound.ProteaAudio
import Control.Monad (unless)
import Graphics.Gloss.Interface.IO.Game
import Data.Maybe

-- project libraries
import Morph
import Gloss.Display
import IO.Parse
import Theory.Theory
import Proof
import Semantics.SemanticFree
import Gloss.World
import Gloss.Actions
import Gloss.Event



-- =========================
-- The core display function
-- =========================

displayStrings :: Float -> [String] -> [Picture]
displayStrings _ [] = []
displayStrings i (s : l) = Translate 0 i (Text s) : displayStrings (i-180) l

goalColor :: Mode ->  Morph -> Maybe SprawlProof -> Color
goalColor (Play _) m (Just goal)
    | m == sprawlGoal goal = makeColor 0.9 1 0.9 1
    | eqMorph m (sprawlGoal goal) = makeColor 0.9 1 0.9 1
    | otherwise = grey
goalColor _ _ _ = grey

ziploc :: [(Point , Int , Int)] -> [String] -> [(Point , String)]
ziploc [] _ = []
ziploc _ [] = []
ziploc ((p , _ , _) : l) (s : r) = (p , s) : ziploc l r

displayWorldB :: World -> IO Picture
displayWorldB w = fmap darkMode (displayWorld w)

displayWorld :: World -> IO Picture
displayWorld (Load size p f l i ((fa , fm) , fb , fc)) =
    return (Pictures
        (Line [(-(size*3/4) , -(size/2)) , (size*3/4 , -(size/2)) , (size*3/4 , size/2) , (-(size*3/4) , size/2) ,  (-(size*3/4) , -(size/2))] :
        Translate (-size/10) (size*11/24) (Scale (size/3000) (size/3000) (Text ("Load File : " ++ fa ++ concat (reverse f)))) :
        Translate (-size/10+1) (size*11/24) (Scale (size/3000) (size/3000) (Text "Load File")) :
        displayMenu (-size/2) (size*27/64) 0 size (menupop i l) (mouseMenu size p)))
displayWorld (World _ _ (Disp v b , size , ori, _) (_ , _ , _ , _ , _) _ (_ , _ , (_ , s , l , _) , _ , _ , _ , _ , _) _) = return (displayTheory size ori v (l ++ exampleSchemas s) b)
displayWorld w@(World m loc (q@(Edit rel writ) , size , ori , zom) (goal , info , (hist , hi , f) , moder , name) (mx , my) ((_ , _ , _ , _ , why) , _ , (oper , _ , _ , _) , _ , _ , _ , comment , file) ext) =
    let rightBar = displayRightbar w file q size (mx , my) ori info m ext in
    let (smorph , stext) = case writ of
                    Editoper (s@(Sig c (_ , st) i j))  
                                ->  (operMorph (Base s) , c ++ " : " ++ show i ++ " -> " ++ show j ++ "  [" ++ st ++ "]" )
                    _           ->  (m , "") in
    let mainpic = scale 1 (-1) (reOrient size ori (zoomPic size zom ori (pictures (fst (pictureMorphI size ori smorph loc))))) in
    return (pictures ([
        color grey (Polygon [((-size)*9/20,(-size)*9/20) , (size*9/20,(-size)*9/20) ,  (size*9/20, size*9/20) , ((-size)*9/20, size*9/20)])  ,
        translate ((-size)/2) (size/2) mainpic ,
        Color white (Polygon [(-size/2 ,-size/2) , (-size/2 , size/2) , (-size , size/2) , (-size ,-size/2)]) ,
        Color white (Polygon [( size/2 ,-size/2) , ( size/2 , size/2) , ( size , size/2) , ( size ,-size/2)]) ,
        -- right bar
        pictures rightBar ,
        translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text stext)) ,
        -- left bar
        translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper)) 
        ,
        Line [((-size)/2,(-size)/2) , ((-size)/2, size/2)] ,
        Line [(size/2,(-size)/2) , (size/2, size/2)]
        ]
        ++ displayInfo size ((-size)*((32-2*stringSplitSkip 135 comment)/64)) (stringSplit 135 comment)
        ++ [Color grey (Polygon [(- size ,-size/2) , (- size , -size) , (size , -size) , (size ,-size/2)]) ,
            Color grey (Polygon [(- size , size/2) , (- size , size) , (size , size) , (size , size/2)])]
        ))
displayWorld w@(World m loc (q , size , ori , zom) (goal , info , (hist , hi , f) , moder , name) (mx , my) ((_ , _ , _ , _ , why) , _ , (oper , _ , _ , _) , _ , _ , _ , comment , file) ext) =
    --let (_ , points) = pictureMorphI size ori m loc in
    let sem = [] in --ziploc points ["a" | _ <- [0..100]] in 
    let c = goalColor q m goal in
    let rightBar = displayRightbar w file q size (mx , my) ori info m ext in
    let mainpic = scale 1 (-1) (reOrient size ori (zoomPic size zom ori (pictures (fst (pictureMorphI size ori m loc))))) in
    return (pictures ([
        color c (Polygon [((-size)*9/20,(-size)*9/20) , (size*9/20,(-size)*9/20) ,  (size*9/20, size*9/20) , ((-size)*9/20, size*9/20)])  ,
        displayExtra size ext ori zom ,
        translate ((-size)/2) (size/2) mainpic ,
        Color white (Polygon [(-size/2 ,-size/2) , (-size/2 , size/2) , (-size , size/2) , (-size ,-size/2)]) ,
        Color white (Polygon [( size/2 ,-size/2) , ( size/2 , size/2) , ( size , size/2) , ( size ,-size/2)]) ,
        -- right bar
        pictures rightBar ,
        -- left bar
        translate ((-size)*3/4) (size*(3-f)/8) (displayScrollPosI moder why size ori mx my hist hi goal name)
        ,
        Line [((-size)/2,(-size)/2) , ((-size)/2, size/2)] ,
        Line [(size/2,(-size)/2) , (size/2, size/2)]
        ]
        ++ displayInfo size ((-size)*((32-2*stringSplitSkip 135 comment)/64)) (stringSplit 135 comment)
        ++ [translate (x-size/2) (-y+size/2) (Text s) | ((x , y) , s) <- sem]
        ++ [Color grey (Polygon [(- size ,-size/2) , (- size , -size) , (size , -size) , (size ,-size/2)]) ,
            Color grey (Polygon [(- size , size/2) , (- size , size) , (size , size) , (size , size/2)])]
        ))
--displayWorld (World {}) = return Blank

gsString :: Maybe Morph -> String
gsString Nothing = "Start"
gsString (Just _) = "Goal"

-- edit display
editDisplay :: Float -> Orient -> [Sig] -> Mode -> [Picture]
editDisplay _ _ _ _ = []
-- editDisplay size ori oper (WRel WDef x) =
--     [Translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text ("Make Definition " ++ gsString x))) ,
--     hbold (Translate (size/2) (size*11/32) (scale (size/4000) (size/4000) (Text "Make Definition"))) ,
--     Translate (size/2) (size*10/32) (scale (size/4000) (size/4000) (Text "Make Lemma")) ,
--     translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper))]
-- editDisplay size ori oper (WRel WLem x) =
--     [Translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text ("Make Lemma " ++ gsString x))) ,
--     Translate (size/2) (size*11/32) (scale (size/4000) (size/4000) (Text "Make Definition")) ,
--     hbold (Translate (size/2) (size*10/32) (scale (size/4000) (size/4000) (Text "Make Lemma"))) ,
--     translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper))]
-- editDisplay size ori oper (WOpe d Nothing _) =
--     [Translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text (d ++ " : ? -> ?"))) , translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper))]
-- editDisplay size ori oper (WOpe d (Just a) _) =
--     [Translate (-size/3) (size/3) (scale (size/2000) (size/2000) (Text (d ++ " : " ++ show a ++ " -> ?"))) , translate ((-size)*3/4) 0 (pictures (displayOper True size ori (size/2) oper))]


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
axiomOnly :: [Relat] -> [Relat]
axiomOnly [] = []
axiomOnly ((mr , m , n , nam , Axiom) : l) = (mr , m , n , nam , Axiom) : axiomOnly l
axiomOnly (_ : l) = axiomOnly l


displayTheory :: Float -> Orient -> Int -> [Relat] -> Bool -> Picture
displayTheory size ori i l b =
    let l' = if b then l else axiomOnly l in
    let (_ , p) = displayTheory' size ori 1 0 l' in
        Translate (-(size*3/4) + fromIntegral i*size*5/24) (size/2.25) (Pictures p)
--displayRelat :: Float -> Orient -> Int -> Relat -> Picture

displayTheory' :: Float -> Orient -> Int -> Int -> [Relat] -> (Int , [Picture])
displayTheory' _ _ i _ [] = (i , [])
displayTheory' size ori i j ((x , m , n , s , w) : l)
--    |   m > n       =   displayTheory' size ori i j l
    |   j <= 10      =   let (k , p) = displayTheory' size ori i (j+5) l in
                        (k ,
                        Translate (size*fromIntegral i/32) (20 - (size*fromIntegral j/16)) (scale 0.12 0.12 (Text (uptoBar s)))
                        : Translate (size*fromIntegral i/32) (- (size*fromIntegral j/16)) (scale 1 (-1) (pictures (pictureMorphBoxO True (size/8) ori (0,0) (RI m))))
                        : Translate (size*fromIntegral i/32) (- (size*fromIntegral (j+2)/16)) (scale 1 (-1) (pictures (pictureMorphBoxO True (size/8) ori (0,0) (RS x n "" w))))
                        : p)
    |   otherwise   =   displayTheory' size ori (i+5) 0 ((x , m , n , s , w) : l)



displayExtra :: Float -> Extra -> Orient -> Zoom -> Picture
displayExtra _ (_ , _ , Nothing , _ , _) _ _ = Blank
displayExtra size (_ , _ , Just (Popbox (x , y) r' , f) , _ , _) ori zom =
    let r = (r'*(2-f)) in
    let r2 = r*0.9 in
    Scale 1 (-1) (Translate (-size/2) (-size/2) (reOrient size ori (
    zoomPic size zom ori (
        Pictures [
            Color (makeColor 1 1 1 f) (Polygon [(x-r , y-r) , (x+r, y-r) , (x+r , y+r) , (x-r , y+r) , (x-r , y-r)]) ,
            Color (greyAlpha f) (Polygon [(x-r2 , y-r2) , (x+r2, y-r2) , (x+r2 , y+r2) , (x-r2 , y+r2) , (x-r2 , y-r2)]) ,
            Color (dkgreyAlpha f) (Line [(x-r , y-r) , (x+r, y-r) , (x+r , y+r) , (x-r , y+r) , (x-r , y-r)]) ,
            Color (dkgreyAlpha f) (Line [(x-r-1 , y-r-1) , (x+r+1, y-r-1) , (x+r+1 , y+r+1) , (x-r-1 , y+r+1) , (x-r-1 , y-r-1)])
        ]))))

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





displayMenu :: Float -> Float -> Int -> Float -> [String] -> Int -> [Picture]
displayMenu _ _ _ _ [] _ = []
displayMenu x y i size (s : l) p
--    |   i < 30 && p == 0    =   Translate x y (scale (size/7000) (size/7000) (Text s)) :
--                                Translate (x-1) (y) (scale (size/7000) (size/7000) (Text s)) : displayMenu x (y + (-size)/32) (i+1) size l (p-1)
    |   i < 20              =   displayMenuBox size (x,y-size/256) s (p == 0) 2
                                --Color grey (Polygon [(x,y-size/256) , (x+size/3.5,y-size/256) , (x+size/3.5, y+ size*5/256) , (x, y+ size*5/256)])
                                -- : Translate x y (scale (size/7000) (size/7000) (Text s))
                                : displayMenu x (y + (-size)/24) (i+1) size l (p-1)
    |   otherwise           =   displayMenu (x + size/2) (y+size*20/24) 0 size (s : l) p

scrollPos :: Float -> Float -> Int -> Float
scrollPos size y n
    |   n <= 2      =   -1
    |   otherwise   =   (fromIntegral n-2) * (y / size) - 1

displayScrollPosI :: MR -> Why -> Float -> Orient -> Float -> Float -> SprawlProof -> Int -> Maybe SprawlProof -> String -> Picture
displayScrollPosI moder why size ori x y hist hi goal name =
    --let v = if x <= 0 then scrollPos size y (length l + length r) else fromIntegral (length l - 2 - hi) in --fromIntegral (length l) - 2 in
    let v = fromIntegral (hi - 1) in
    let rews = (sprawlProofRewBranch hist  ++ fmap (\z -> (z , False)) (proofSeqM (fmap sprawlProofTrace goal))) in
        Translate 0 (v*size/4) (Pictures (
            --(if v == -1 && length l > 1 then translate 0 (size/6) (scale (size/2000) (size/2000) (Text "Animate")) else Blank) :
            translate 4 (20 + size/24) (scale (size/2000) (size/2000) (Text (show why))) :
            translate 5 (20 + size/24) (scale (size/2000) (size/2000) (Text (show why))) :
            translate 4 20 (scale (size/5000) (size/5000) (Text name)) :
            translate 4 21 (scale (size/5000) (size/5000) (Text name)) :
            displayScrollPos moder size ori 0 v rews hi (lengthSprawlProofM goal )))

displayScrollPos :: MR -> Float -> Orient -> Float -> Float -> [(Rew , Bool)] -> Int -> Int -> [Picture]
displayScrollPos moder size _ c _ [] _ n =
                                let y = (c + fromIntegral n * size/4) in
                                [
                                color black (Polygon [(0 , y+size/200) , (0 , y-(size/200)) , (size/4 , y-(size/200)) , (size/4 , y+size/200)]) ,
                                translate (size/8) y (signPre black white (size/128) (mrRew moder))
                                ]
displayScrollPos moder size ori c y ((x , b) : l) hi n
    |   y <= -4             =   displayScrollPos moder size ori (c + (-size)/4) (y-1) l (hi-1) n
    |   y >= 2              =   displayScrollPos moder size ori (c + (-size)/4) (y-1) l (hi-1) n
    |   hi == 0             =   color dkgrey (translate 0 c (Polygon [(0 ,0) , (0 ,(-size)/4) , (size/4 ,(-size)/4) , (size/4 ,0) , (0 ,0)]))
                                : (if b then Line [(size/32, c+size/160) , (size*7/32 , c+size/160)] else Blank)
                                : translate 0 c (scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0,0) x)))
                                : displayScrollPos moder size ori (c + (-size)/4) (y-1) l (hi-1) n
    |   otherwise           =   (if b then Line [(size/32, c+size/160) , (size*7/32 , c+size/160)] else Blank)
                                : translate 0 c (scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0,0) x)))
                                : displayScrollPos moder size ori (c + (-size)/4) (y-1) l (hi-1) n

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

displayRightbar :: World -> String -> Mode -> Float -> Point -> Orient -> Maybe (Rew , Morph , [Rew] , Float) -> Morph -> Extra -> [Picture]
displayRightbar w name q@(Edit rel@(mr , start , goal , nam , why) writ) size (mx , my) ori Nothing m ext =
            [translate (size*0.51) (size*0.46) (scale (size/6000) (size/6000) (Text name)) ,
            translate (size*0.51+1) (size*0.46) (scale (size/6000) (size/6000) (Text name)) ,
            translate (size*0.51) (size*0.4) (color grey (Polygon [(0 ,-size/128) , (size*14/64 ,-size/128) , (size*14/64 , size/40) , (0 , size/40)])) ,
            translate (size*0.51) (size*0.4) (scale (size/5000) (size/5000) (Text "Load File")) ,
            if mx >= size && my <= size/8 then translate (size*0.51+1) (size*0.4) (scale (size/5000) (size/5000) (Text "Load File")) else Blank ,
            Line [(size/2 , size*3/8) , (size*3/4 , size*3/8)] ,
            translate (size/2+size/64) (size*9/24-size/32) (scale (size/5000) (size/5000) (Text (if writ == Editname then nam ++ "|" else nam))) ,
            displayMenuBox size (size/2 , size*8/24) "Rename" False 1 ,
            displayMenuBox size (size/2 , size*7/24) ("Toggle: " ++ show why) False 1 ,
            translate (size/2) (size/4) (scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0 , 0) (RI start)))) ,
            translate (size/2) 0 (scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0 , 0) (RS mr goal "" why)))) ,
            displayMenuBox size (size/2 , -size*6/24) ("Toggle: " ++ saveMR mr) False 1 ,
            displayMenuBox size (size/2 , -size*7/24) (if relatCheck rel then "Finish/save" else "<type error>") False 1 ,
            displayMenuBox size (size/2 , -size*8/24) (if isEditoper writ then "Save op" else "Create new op") False 1 ,
            Line [(size/2 , -size*9/24) , (size*3/4 , -size*9/24)] ,
            displayMenuBox size (size/2 , -size*10/24) "Exit Edit" False 1
            ]
displayRightbar w name _ size (mx , my) ori Nothing m ext =
            translate (size*0.51) (size*0.46) (scale (size/6000) (size/6000) (Text name)) :
            translate (size*0.51+1) (size*0.46) (scale (size/6000) (size/6000) (Text name)) :
            translate (size*0.51) (size*0.4) (color grey (Polygon [(0 ,-size/128) , (size*14/64 ,-size/128) , (size*14/64 , size/40) , (0 , size/40)])) :
            translate (size*0.51) (size*0.4) (scale (size/5000) (size/5000) (Text "Load File")) :
            (if mx >= size && my <= size/8 then translate (size*0.51+1) (size*0.4) (scale (size/5000) (size/5000) (Text "Load File")) else Blank) :
            Line [(size/2 , size*3/8) , (size*3/4 , size*3/8)] :
            Line [(size/2 , 0) , (size*3/4 , 0)] :
            displayOptions size (size/2 ,0) (selectOption size (mx , my)) 0 (optionsNames w) ++
            let (_ , _ , _ , _ , stri2) = ext in
            let stri = if null stri2 then lines (printMorphI m) else stri2 in
            let v = 9 / int2Float (max 9 (length stri)) in
            [translate (size*0.51) (size*0.335) (scale (v*size/5000) (v*size/5000)
            (Pictures (displayStrings 0 stri))) ,
            translate (size*0.51) (size*0.335+1) (scale (v*size/5000) (v*size/5000)
            (Pictures (displayStrings 0 stri)))
            ]
displayRightbar w _ _ size _ ori (Just (_ , _ , info , f)) _ _ =   case displayWheelInfo info of
    Nothing                 ->  []
    Just (m , Nothing)      ->  [translate (size/2) (size/8) (scale 1 (-1) (pictures (pictureMorphBoxO True (size/4) ori (0,0) m)))]
    Just (m , Just (x , y , z , w))
                            ->  [
                                color dkgrey (translate (size/2) (size*(1+f)/8) (Polygon [(0 ,0) , (0 ,(-size)/4) , (size/4 ,(-size)/4) , (size/4 ,0) , (0 ,0)])) ,
                                translate (size/2) (size*(1+f)/8) (scale 1 (-1) (pictures (pictureMorphBoxO False (size/4) ori (0,0) m))) ,
                                translate (size/2) (size*(3+f)/8) (scale 1 (-1) (pictures (pictureMorphBoxO False (size/4) ori (0,-0.2) z))) ,
                                translate (size/2) (size*(5+f)/8) (scale 1 (-1) (pictures (pictureMorphBoxO False (size/4) ori (0,-0.4) w))) ,
                                translate (size/2) (size*(f-1)/8) (scale 1 (-1) (pictures (pictureMorphBoxO False (size/4) ori (0,0.2) x))) ,
                                translate (size/2) (size*(f-3)/8) (scale 1 (-1) (pictures (pictureMorphBoxO False (size/4) ori (0,0.4) y)))]

                                --[translate (size/2) (size/8) (scale 1 (-1) (pictures (pictureMorphBoxO False (size/4) ori (0,0) m))) ,
                                --translate (size*33/64) (size*11/32) (scale (7/8) (-(7/8)) (pictures (pictureMorphBoxO False (size/4) ori (0,-0.2) z))) ,
                                --translate (size*35/64) (size/2) (scale (5/8) (- (5 / 8)) (pictures (pictureMorphBoxO False (size/4) ori (0,-0.4) w))) ,
                                --translate (size*33/64) ((-size)/8) (scale (7/8) (- (7 / 8)) (pictures (pictureMorphBoxO False (size/4) ori (0,0.2) x))) ,
                                --translate (size*35/64) ((-size)*11/32) (scale (5/8) (- (5 / 8)) (pictures (pictureMorphBoxO False (size/4) ori (0,0.4) y)))]


optionsNameProof :: World -> String
optionsNameProof w =
    let (goal , _ , (hist , i , _) , _ , _) = winfo w in
    let (rel , _ , _ , _ , d , _ , _ , _) = document w in
    case d of
        Displ _ Nop _ _ _ _ ->
            if relatWhy rel /= Lemma then "Asserted" else
            if proofCheck hist i goal then "Save proof"
            else "No proof"
        Displ _ (Yep p _ _) _ _ _ _ ->
            if proofCheck hist i goal then (if i >= length (snd p) then "!!Overwrite proof!!" else "!Overwrite proof!")
            else "Load proof"
        _                   ->  "No proof"

optionsNames :: World -> [String]
optionsNames w =
    ["r: Rewrites List" ,
    "o: Orientation" ,
    "a: Auto-reduce" , "z: Zoom in box" , "Save rewrite*" , "Partial Split*" , "-" , "Go to Edit" , optionsNameProof w , "<: Previous page" , ">: Next page"]



dangerOption :: Int -> Bool
dangerOption 4 = True
dangerOption 5 = True
dangerOption 8 = True
dangerOption _ = False

displayOptions :: Float -> Point -> Int -> Int -> [String] -> [Picture]
displayOptions _ _ _ _ [] = []
displayOptions size (x , y) i j (s : l) =   
    displayMenuBox size (x , y) s (i == 0) 1
    : displayOptions size (x , y - size/24) (i-1) (j+1) l

displayMenuBox :: Float -> Point -> String -> Bool -> Float -> Picture
displayMenuBox size (x , y) s b wi = 
            Pictures [
                color (if b then white else grey) (Polygon [(x + size/96 , y-size/168) , (x + size*(24*wi-1)/96 , y-size/168) , (x + size*(24*wi-1)/96 , y-size/28) , (x + size/96 , y-size/28)])
                , translate (x+size/64) (y-size/32) (scale (size/5000) (size/5000) (Text s))]





-- display Options
displayOper :: Bool -> Float -> Orient -> Float -> [Sig] -> [Picture]
displayOper b size ori y ((Sig c s i j) : l) =
    let xt = if b then (size/11) else (size/7) in
    [translate (size/32) (y + (-size)/16) (scale (size/3000) (size/3000) (Text c)) ,
    translate xt (y - size/80) (scale 1 (-1) (reOrient (size/12) ori (pictures (pictureMorphStat (size/12) ori (operMorph (Base (Sig c s i j))))))) ]
    --(pictures (pictureMorphStat (size/12) ori (operMorph (Base (Sig c s i j))))))]
    ++ (displayOper (not b) size ori (y + (-size)/20) l)
displayOper _ _ _ _ _ = []






-- Start application from loading a file
playLoad :: Bool -> Maybe Int -> Bool -> Settings -> Orient -> Bool -> IO ()
playLoad full ss dm (filepath , music) ori zo =
    screenz full ss >>= \size ->
    loadFileInit size [] ((filepath , music) , ori , zo) >>= \w ->
    do
        initialized <- initAudio 64 44100 1024
        unless initialized $ fail "Failed to initialize the audio system"

        playIO (setDisplay full size)
            (if dm then setColorB else setColor)
            setSim
            w
            (if dm then displayWorldB else displayWorld)
            event
            step