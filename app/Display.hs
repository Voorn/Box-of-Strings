{-# OPTIONS_GHC -Wno-type-defaults #-}
module Display where

-- Standard libraries
import Data.Bifunctor

-- Extended libraries
import Graphics.Gloss

-- Internal libraries
import Morph

-- ==========================================================
-- Module for Generating vector Gloss pictures from morphisms
-- ==========================================================

-- Vector/Line segment data type, simply given by two points
type Vect = (Point , Point)

-- Orientation type for string diagram: LR is left to right, UD is top to bottom.
-- If you want bottom to top or right to left, just define the theory in reverse
data Orient =
    LR
    |   UD


-- Applying reorientation to a picture element
reOrient :: Float -> Orient -> Picture -> Picture
reOrient _ LR p = p
reOrient _ UD p = Rotate 270 (scale 1 (-1) p)

-- Deorienting a character to ensure it stays in readable position
-- Reorientation is applied to the whole picture, including characters, so character needs to be de-oriented
charOrient :: Float -> Orient -> Char -> Picture
charOrient _ LR c = Text [c]
charOrient _ UD c = Translate 70 70 (Rotate 90 (scale 1 (-1) (Text [c])))

-- Applying reorientation to a point
rePoint :: Orient -> Point -> Point
rePoint LR p = p
rePoint UD (x , y) = (y , x)

-- Toggle orientations
flipOrient :: Orient -> Orient
flipOrient LR = UD
flipOrient UD = LR

-- Some basic colors for use
grey :: Color
grey = makeColorI 240 240 240 255

ltgrey :: Color
ltgrey = makeColorI 247 247 247 255

dkgrey :: Color
dkgrey = makeColorI 180 180 180 255

-- ===========================
-- Display
-- ===========================

-- Cannonical location of nodes in a morphism
initCoor :: Float -> Morph -> [(Float , Float)]
initCoor s m = [(s * a , s * b) | (a , b) <- coorMorph m]

initCoor' :: Float -> Morph -> [(Float , Float , Bool)]
initCoor' s m = [(s * a , s * b , False) | (a , b) <- coorMorph m]

-- Calculates how much space can be given to boxes and operations, giving them a size
boxsize :: Float -> Morph -> Float
boxsize h m =  h / (2*sizeMorph' m)

-- Draw a static morphism in a box, using orientation
pictureMorphBoxO :: Bool -> Float -> Orient -> (Float , Float) -> Rew -> [Picture]
pictureMorphBoxO b h ori (x , y) m =
    let (l, r, u, d) = (h*(0.05-x/20) , h*(0.95-x/20) , h*(0.05-y/20) , h*(0.95-y/20)) in
    color ltgrey (Polygon [(0,0) , (l,u),(r,u),(h,0)]) :
    color ltgrey (Polygon [(0,h) , (l,d),(r,d),(h,h)]) :
    color dkgrey (Line [(0,0) , (0,h) , (h,h) , (h,0) , (0,0)]) :
    color grey (Polygon [(l,u),(l,d),(r,d),(r,u)]) :
    fmap (reOrient h ori) (pictureMorphStat h ori (rewMorph m)) ++
    [Translate (if b then h/2 else h/12) (if b then 0 else h/12) (signPre white black (h/32) m)]

-- Draw a static morphism in a box
pictureMorphBox :: Bool -> Float -> Orient -> (Float , Float) -> Rew -> [Picture]
pictureMorphBox b h ori (x , y) m =
    let (l, r, u, d) = (h*(0.05-x/20) , h*(0.95-x/20) , h*(0.05-y/20) , h*(0.95-y/20)) in
    color ltgrey (Polygon [(0,0) , (l,u),(r,u),(h,0)]) :
    color ltgrey (Polygon [(0,h) , (l,d),(r,d),(h,h)]) :
    color dkgrey (Line [(0,0) , (0,h) , (h,h) , (h,0) , (0,0)]) :
    color grey (Polygon [(l,u),(l,d),(r,d),(r,u)]) :
    pictureMorphStat h ori (rewMorph m) ++
    [Translate (if b then h/2 else h/12) (if b then 0 else h/12) (signPre white black (h/32) m)]

-- Draw a static picture using standard coordinates
pictureMorphStat :: Float -> Orient -> Morph -> [Picture]
pictureMorphStat h ori m =
    fst (pictureMorphI h ori m (initCoor' h m))

-- Dynamic picture of a morphism using input coordinates: Initialisation
pictureMorphI :: Float -> Orient -> Morph -> [(Float , Float , Bool)] -> ([Picture] , [(Point , Int , Int)])
pictureMorphI h ori m loc = let (_ , i) = typeMorph m in
                        let (mp , mq , mn , ml) = pictureMorph 1 h ori (boxsize h m) m loc in
                        let (ep , el) = pictureMorphEnd (boxsize h m) (lengthMorph m - 1) h 0 i mn in
                            (mp ++ ep ++ mq , ml ++ el)

-- Recursor
pictureMorph :: Int -> Float -> Orient -> Float -> Morph -> [(Float , Float , Bool)] -> ([Picture] , [Picture] , [Vect] , [(Point , Int , Int)])
pictureMorph _ h _ _ (Start i) _ = ([] , [] , [((0 , h * frac2Float (1+j , i+1)) , (1 , 0)) | j <- [0..i-1]] , [])
-- was tweaked to be slightly more narrow. It was 1+j / 1+i
pictureMorph _ _ _ _ _ [] = ([] , [] , [] , [])
pictureMorph l h ori bh (Op m i o) ((x , y , b) : r) =
    let (oi , oo) = typeOper o in
    let (mp , mq , mnotch , mlin) = pictureMorph (l+1) h ori bh m r in
    case o of
        Comp n _ -> let os = sizeOper o in
                    let (lp , lnotch , llin) = notchLine h l 0 i oi oi oo (os*bh) (os*bh) bh x y mnotch in
                    let mini = translate (x-bh*os) (y-bh*os) (pictures (pictureMorphBox False (2*os*bh) ori (x/h-0.5,y/h-0.5) n)) in
                    let box = [color white (
                                Polygon [(x-bh*os , y-bh*os) , (x+bh*os , y-bh*os) , (x+bh*os , y+bh*os) , (x-bh*os , y+bh*os) , (x-bh*os , y-bh*os)]) ,
                                Line [(x-bh*os , y-bh*os) , (x+bh*os , y-bh*os) , (x+bh*os , y+bh*os) , (x-bh*os , y+bh*os) , (x-bh*os , y-bh*os)] ,
                                mini] in
                    if b then
                        (mp ++ lp  , mq ++ box , lnotch , mlin ++ llin)
                    else
                        (box ++ mp ++ lp , mq , lnotch , mlin ++ llin)
        -- Symbol in circle-box
        Base (Sig c "0" _ _) ->
                    let (lp , lnotch , llin) = notchLineCirc h l 0 i oi oi oo bh bh x y mnotch in
                    let tex = translate (x-bh/2.5) (y+bh/2) (scale (bh*0.012) (-(bh*0.012)) (Text [c])) in
                    --let tex = pictureSpider bh (2*bh) x y oi oo in
                    (Translate x y (Circle bh) :  tex : mp ++ lp , mq , lnotch , mlin ++ llin)
        -- No symbol, just connections
        Base (Sig _ "3" _ _) ->
                    let (lp , lnotch , llin) = notchLineCirc h l 0 i oi oi oo 0 bh x y mnotch in
                    --let tex = pictureSpider bh (2*bh) x y oi oo in
                    (mp ++ lp , mq , lnotch , mlin ++ llin)
        -- Black bullet connection
        Base (Sig _ "2" _ _) ->
                    let (lp , lnotch , llin) = notchLineCirc h l 0 i oi oi oo (bh/8) bh x y mnotch in
                    --let tex = pictureSpider bh (2*bh) x y oi oo in
                    (mp ++ lp , octagon (max 1.5 (bh/8)) x y :
                        mq , lnotch , mlin ++ llin)
        Base (Sig _ "w" _ _) ->
                    let (lp , lnotch , llin) = notchLineCirc h l 0 i oi oi oo (bh/8) bh x y mnotch in
                    --let tex = pictureSpider bh (2*bh) x y oi oo in
                    (mp ++ lp , woctagon (max 1.5 (bh/8)) x y :
                        mq , lnotch , mlin ++ llin)
        -- Swap-slash
        Base (Sig _ "1" _ _) ->
                    let (lp , lnotch , llin) = notchLineCirc h l 0 i oi oi oo (max 2 (bh/8) * 2.8) bh x y mnotch in
                    --let tex = pictureSpider bh (2*bh) x y oi oo in
                    (mp ++ lp , slash (max 2 (bh/8)) x y :
                        mq , lnotch , mlin ++ llin)
        -- Swap-slash inverted
        Base (Sig _ "4" _ _) ->
                    let (lp , lnotch , llin) = notchLineCirc h l 0 i oi oi oo (max 4 (bh/4)) bh x y mnotch in
                    --let tex = pictureSpider bh (2*bh) x y oi oo in
                    (mp ++ lp , dash (max 2 (bh/8)) x y :
                        mq , lnotch , mlin ++ llin)
        Base (Sig _ "5" _ _) ->
                    let (lp , lnotch , llin) = notchLineCirc2 h l 0 i oi oi oo 0 bh x y mnotch in
                    --let tex = pictureSpider bh (2*bh) x y oi oo in
                    (mp ++ lp , mq , lnotch , mlin ++ llin)
        Base (Sig _ "8" _ _) ->
                    let (lp , lnotch , llin) = notchLine h l 0 i oi oi oo bh (2*bh) bh x y mnotch in
                    let tex = pictureSpider bh (2*bh) x y oi oo in
                    (mp ++ lp , tex ++ mq , lnotch , mlin ++ llin)
        Base (Sig _ "9" _ _) ->
                    let (lp , lnotch , llin) = notchLine h l 0 i oi oi oo bh (2*bh) bh x y mnotch in
                    let tex = pictureSpider bh (2*bh) x y oi oo in
                    (mp ++ lp , octagon (bh/5) x y : tex ++ mq , lnotch , mlin ++ llin)
        Base (Sig _ "qd" _ _) ->
                    let (lp , lnotch , llin) = notchLine h l 0 i oi oi oo bh (2*bh) bh x y mnotch in
                    let tex = pictureQuantumD bh (2*bh) x y oi oo in
                    (mp ++ lp , tex ++ mq , lnotch , mlin ++ llin)
        Base (Sig _ "qu" _ _) ->
                    let (lp , lnotch , llin) = notchLine h l 0 i oi oi oo bh (2*bh) bh x y mnotch in
                    let tex = pictureQuantumU bh (2*bh) x y oi oo in
                    (mp ++ lp , tex ++ mq , lnotch , mlin ++ llin)
        Base (Sig _ "v" _ _) ->
                    let (lp , lnotch , llin) = notchLineVert h l 0 i oi oi oo 0 bh x y mnotch in
                    (mp ++ lp , mq , lnotch , mlin ++ llin)
        Base (Sig c  "" _ _) ->
                    let (lp , lnotch , llin) = notchLine h l 0 i oi oi oo bh bh bh x y mnotch in
                    let tex = translate (x-bh/2.5) (y+bh/2) (scale (bh*0.012) (-(bh*0.012)) (charOrient bh ori c)) in
                    if b then
                        (mp ++ lp , mq ++ octBox x y bh (bh * 0.8) ++ [tex] , lnotch , mlin ++ llin)
                    else
                        (octBox x y bh (bh * 0.8) ++ tex : mp ++ lp , mq , lnotch , mlin ++ llin)
        Base (Sig s  _ _ _) ->
                    let (lp , lnotch , llin) = notchLine h l 0 i oi oi oo (2*bh) bh bh x y mnotch in
                    let tex = translate (x-bh*1.5) (y+bh/2) (scale (bh*0.012) (-(bh*0.012)) (charOrient bh ori s)) in
                    if b then
                        (mp ++ lp , mq ++ octBox2 x y bh (bh * 0.8) ++ [tex] , lnotch , mlin ++ llin)
                    else
                        (octBox2 x y bh (bh * 0.8) ++ tex : mp ++ lp , mq , lnotch , mlin ++ llin)

-- Connecting the strings to the right side
pictureMorphEnd :: Float -> Int -> Float -> Int -> Int -> [Vect] -> ([Picture] , [(Point , Int , Int)])
pictureMorphEnd _ _ _ _ _ [] = ([] , [])
pictureMorphEnd bh d h i j (a : notches) =
    let (ep , el) = pictureMorphEnd bh d h (i+1) j notches in
    let (linepic , linepoint) = picLine (bh*3) (h/250) a  ((h , h * frac2Float (1+i , 1+j)) , (-1 , 0)) in
-- tweaked: 1+2*i / 1+2*j
    (linepic ++ ep ,
    (linepoint , 0 , i) : el)

-- =====================================
-- Drawing Operations and their elements
-- =====================================

-- Drawing a box with chipped corners
octBox :: Float -> Float -> Float -> Float -> [Picture]
octBox x y a b = [color white (Polygon [(x-a , y-b) , (x-b , y-a) , (x+b , y-a) , (x+a , y-b) , (x+a , y+b) , (x+b , y+a) , (x-b , y+a) , (x-a , y+b)]) ,
    Line [(x-a , y-b) , (x-b , y-a) , (x+b , y-a) , (x+a , y-b) , (x+a , y+b) , (x+b , y+a) , (x-b , y+a) , (x-a , y+b) , (x-a , y-b)]]

octBox2 :: Float -> Float -> Float -> Float -> [Picture]
octBox2 x y a b = [color white (Polygon [(x-a*2 , y-b) , (x-b-a , y-a) , (x+b+a , y-a) , (x+a*2 , y-b) , (x+a*2 , y+b) , (x+b+a , y+a) , (x-b-a , y+a) , (x-a*2 , y+b)]) ,
    Line [(x-a*2 , y-b) , (x-b-a , y-a) , (x+b+a , y-a) , (x+a*2 , y-b) , (x+a*2 , y+b) , (x+b+a , y+a) , (x-b-a , y+a) , (x-a*2 , y+b) , (x-a*2 , y-b)]]

-- Drawing legs of spider style operation
pictureSpider :: Float -> Float -> Float -> Float -> Int -> Int -> [Picture]
pictureSpider w h x y i j =
    [spiderLeg (x-w) (y + h*frac2Float (1+2*a-i , i)) x y  | a <- [0..i-1]]
    ++ [spiderLeg (x+w) (y + h*frac2Float (1+2*a-j , j)) x y  | a <- [0..j-1]]

spiderLeg :: Float -> Float -> Float -> Float -> Picture
spiderLeg x1 y1 x2 y2 = Line [(x1 + i*(x2-x1)/8 , y1 + (1 - cos (pi*i/16))*(y2-y1)) | i <- [0..8]]

-- Drawing quantum gates 
pictureQuantumD :: Float -> Float -> Float -> Float -> Int -> Int -> [Picture]
pictureQuantumD w h x y i _ =
    woctagon (h/12) x (y + h*frac2Float (i-1 , i+1)) :
    octagon (h/12) x (y + h*frac2Float (-i+1 , i+1)) :
    Line [(x , y + h*frac2Float (i-1 , i+1) + h/6) , (x , y + h*frac2Float (-i+1 , i+1))] :
    [Line [(x-w , y + h*frac2Float (2*a-i-1 , i+1)) , (x + w , y + h*frac2Float (2*a-i-1 , i+1))] | a <- [1..i]]

pictureQuantumU :: Float -> Float -> Float -> Float -> Int -> Int -> [Picture]
pictureQuantumU w h x y i _ =
    octagon (h/12) x (y + h*frac2Float (i-1 , i+1)) :
    woctagon (h/12) x (y + h*frac2Float (-i+1 , i+1)) :
    Line [(x , y + h*frac2Float (i-1 , i+1)) , (x , y + h*frac2Float (-i+1 , i+1) - h/6)] :
    [Line [(x-w , y + h*frac2Float (2*a-i-1 , i+1)) , (x + w , y + h*frac2Float (2*a-i-1 , i+1))] | a <- [1..i]]

-- Drawing a black dot (called since it used to be an octagon, now it is a more a circle)
octagon :: Float -> Float -> Float -> Picture
octagon w x y = Polygon [   (x-w*1.4 , y-w*1.4) , (x-w*0.5 , y-w*2) , (x+w*0.5 , y-w*2) ,
                            (x+w*1.4 , y-w*1.4) , (x+w*2 , y-w*0.5) , (x+w*2 , y+w*0.5) ,
                            (x+w*1.4 , y+w*1.4) , (x+w*0.5 , y+w*2) , (x-w*0.5 , y+w*2) ,
                            (x-w*1.4 , y+w*1.4) , (x-w*2 , y+w*0.5) , (x-w*2 , y-w*0.5)]

-- Drawing a white dot with black border
woctagon :: Float -> Float -> Float -> Picture
woctagon w x y = pictures [
    color white (Polygon [  (x-w*1.4 , y-w*1.4) , (x-w*0.5 , y-w*2) , (x+w*0.5 , y-w*2) ,
                            (x+w*1.4 , y-w*1.4) , (x+w*2 , y-w*0.5) , (x+w*2 , y+w*0.5) ,
                            (x+w*1.4 , y+w*1.4) , (x+w*0.5 , y+w*2) , (x-w*0.5 , y+w*2) ,
                            (x-w*1.4 , y+w*1.4) , (x-w*2 , y+w*0.5) , (x-w*2 , y-w*0.5)]) ,
    Line                [   (x-w*1.4 , y-w*1.4) , (x-w*0.5 , y-w*2) , (x+w*0.5 , y-w*2) ,
                            (x+w*1.4 , y-w*1.4) , (x+w*2 , y-w*0.5) , (x+w*2 , y+w*0.5) ,
                            (x+w*1.4 , y+w*1.4) , (x+w*0.5 , y+w*2) , (x-w*0.5 , y+w*2) ,
                            (x-w*1.4 , y+w*1.4) , (x-w*2 , y+w*0.5) , (x-w*2 , y-w*0.5) , (x-w*1.4 , y-w*1.4)]]

-- Crossing wires with \ wire on top
slash :: Float -> Float -> Float -> Picture
slash w x y =
    pictures [
        --color grey (Polygon [(x-w*2 , y-w) , (x-w , y-w*2) , (x+w , y-w*2) , (x+w*2 , y-w) , (x+w*2 , y+w) , (x+w , y+w*2) , (x-w , y+w*2) , (x-w*2 , y+w)]) ,
        Line [(x - w*2 , y - w*2) , (x + w*2 , y + w*2)]]

-- Crossing wires with / wire on top
dash :: Float -> Float -> Float -> Picture
dash w x y =
    pictures [
        --color grey (Polygon [(x-w*2 , y-w) , (x-w , y-w*2) , (x+w , y-w*2) , (x+w*2 , y-w) , (x+w*2 , y+w) , (x+w , y+w*2) , (x-w , y+w*2) , (x-w*2 , y+w)]) ,
        Line [(x - w*2 , y + w*2) , (x + w*2 , y - w*2)]]


-- ================================================
-- Connecting elements: wires in between operations
-- ================================================

-- Connect input strings and return output string positions and directions for a rectangular operation

-- screen_size   current_depth   current_width   front_counter   input_counter   input_total   output_total   box_radius   morphism_x   morphism_y   notches  
-- -> (picture, notches, line_info)
notchLine :: Float -> Int -> Int -> Int -> Int -> Int -> Int -> Float -> Float -> Float -> Float -> Float -> [Vect]
    -> ([Picture] , [Vect] , [(Point , Int , Int)])
notchLine _ _ _ i j _ out bw bh _ x y []
-- tweaked from: 2*v - 1 - out , out
    |   i <= 0 && j <= 0    =   ([] , [((x+bw , y + bh* frac2Float (2*v - 1 - out , out+1)) , (1 , 0)) | v <- [1..out]] , [])
    |   otherwise           =   ([] , [] , [])
notchLine h d w i j inp out bw bh bb x y (((ax , ay) , (adx , ady)) : notch)
    |   i <= 0 && j <= 0    =   ([] , [((x+bw , y + bh* frac2Float (2*v - 1 - out , out+1)) , (1 , 0)) | v <- [1..out]] ++ ((ax , ay) , (adx , ady)) : notch , [])
    |   i <= 0              =   let (rp , rn , rl) = notchLine h d (w+1) i (j-1) inp out bw bh bb x y notch in
                                let (linepic , linepoint) = picLine (bb*3) (h/250) ((ax , ay) , (adx , ady))  ((x-bw , y - bh* frac2Float (2*j - 1 - inp , inp + 1)) , (-1 , 0)) in
                                (linepic ++
                                    rp , rn ,
                                    (linepoint , d , w) : rl)
    |   otherwise           =   let (rp , rn , rl) = notchLine h d (w+1) (i-1) j inp out bw bh bb x y notch in
                                (rp , ((ax , ay) , (adx , ady)) : rn , rl)

-- Computing line segment from radius and direction
radVect :: Point -> Float -> Float -> Vect
radVect (x , y) rad ang =
    let dx = cos ang in
    let dy = sin ang in ((x + rad * dx , y + rad * dy) , (dx , dy))

radSwap :: Point -> Float -> Float -> Vect
radSwap (x , y) rad ang
    | ang <= 0 || (ang > pi /2 && ang <= pi) =  let dx = cos ang in
                                                let dy = sin ang in ((x , y) , (dx , dy))
    | otherwise                              =  let dx = cos ang in
                                                let dy = sin ang in ((x + rad * dx , y + rad * dy) , (dx , dy))

-- Connect input strings and return output string positions and directions for a circular operation
notchLineCirc :: Float -> Int -> Int -> Int -> Int -> Int -> Int -> Float -> Float -> Float -> Float -> [Vect]
    -> ([Picture] , [Vect] , [(Point , Int , Int)])
notchLineCirc _ _ _ i j _ out rad _ x y []
    |   i <= 0 && j <= 0    =   ([] , [radVect (x , y) rad (pi * frac2Float (2*v - 1 - out , out * 2))  | v <- [1..out]] , [])
    |   otherwise           =   ([] , [] , [])
notchLineCirc h d w i j inp out rad bb x y (a : notch)
    |   i <= 0 && j <= 0    =   ([] , [radVect (x , y) rad (pi * frac2Float (2*v - 1 - out , out * 2)) | v <- [1..out]] ++ a : notch , [])
    |   i <= 0              =   let (rp , rn , rl) = notchLineCirc h d (w+1) i (j-1) inp out rad bb x y notch in
                                let (linepic , linepoint) = picLine (bb*3) (h/250) a (radVect (x , y) rad (pi + pi * frac2Float (2*j - 1 - inp , 2 * inp))) in
                                (linepic ++
                                    rp , rn ,
                                    (linepoint , d , w) : rl)
    |   otherwise           =   let (rp , rn , rl) = notchLineCirc h d (w+1) (i-1) j inp out rad bb x y notch in
                                (rp , a : rn , rl)

notchLineCirc2 :: Float -> Int -> Int -> Int -> Int -> Int -> Int -> Float -> Float -> Float -> Float -> [Vect]
    -> ([Picture] , [Vect] , [(Point , Int , Int)])
notchLineCirc2 _ _ _ i j _ out rad _ x y []
    |   i <= 0 && j <= 0    =   ([] , [radVect (x , y) rad (pi * frac2Float (2*v - 2 - out + 1 , out * 2 - 2))  | v <- [1..out]] , [])
    |   otherwise           =   ([] , [] , [])
notchLineCirc2 h d w i j inp out rad bb x y (a : notch)
    |   i <= 0 && j <= 0    =   ([] , [radVect (x , y) rad (pi * frac2Float (2*v - 2 - out + 1 , out * 2 - 2)) | v <- [1..out]] ++ a : notch , [])
    |   i <= 0              =   let (rp , rn , rl) = notchLineCirc2 h d (w+1) i (j-1) inp out rad bb x y notch in
                                let (linepic , linepoint) = picLine (bb*3) (h/250) a (radVect (x , y) rad (pi + pi * frac2Float (2*j - 2 - inp + 1 , 2 * inp - 2))) in
                                (linepic ++
                                    rp , rn ,
                                    (linepoint , d , w) : rl)
    |   otherwise           =   let (rp , rn , rl) = notchLineCirc2 h d (w+1) (i-1) j inp out rad bb x y notch in
                                (rp , a : rn , rl)

-- Connect input strings and return output string positions and directions for a circular operation
notchLineVert :: Float -> Int -> Int -> Int -> Int -> Int -> Int -> Float -> Float -> Float -> Float -> [Vect]
    -> ([Picture] , [Vect] , [(Point , Int , Int)])
notchLineVert _ _ _ i j _ out rad _ x y []
    |   i <= 0 && j <= 0    =   ([] , [radVect (x , y) rad (pi * frac2Float (v , out - 1) - pi/2)  | v <- [0..out-1]] , [])
    |   otherwise           =   ([] , [] , [])
notchLineVert h d w i j inp out rad bb x y (a : notch)
    |   i <= 0 && j <= 0    =   ([] , [radVect (x , y) rad (pi * frac2Float (v , out - 1) - pi/2) | v <- [0..out-1]] ++ a : notch , [])
    |   i <= 0              =   let (rp , rn , rl) = notchLineVert h d (w+1) i (j-1) inp out rad bb x y notch in
                                let (linepic , linepoint) = picLine (bb*3) (h/250) a (radVect (x , y) rad (pi/2 + pi * frac2Float (j - 1 , inp - 1))) in
                                (linepic ++
                                    rp , rn ,
                                    (linepoint , d , w) : rl)
    |   otherwise           =   let (rp , rn , rl) = notchLineVert h d (w+1) (i-1) j inp out rad bb x y notch in
                                (rp , a : rn , rl)

-- ============================
-- The string drawing operation
-- ============================

pictureLine :: Float -> (Float , Float) -> (Float , Float) -> Picture
pictureLine r (x , y) (z , w) = pictures [Line [(x + i*(z-x)/12 , y + (1 - cos (pi*i/12))*(w-y)/2) | i <- [0..12]] , translate ((x+z)/2) ((y+w)/2) (Circle r)]

pictureLine2 :: Float -> Float -> (Float , Float) -> (Float , Float) -> Picture
pictureLine2 h r (x , y) (z , w) = pictures [Line [
    (x + i*(z-x)/12 + max 0 (h+(x-z)/(2*pi)) *sin (pi*i/6) ,
    y + (1 - cos (pi*i/12))*(w-y)/2) | i <- [0..12]] , translate ((x+z)/2) ((y+w)/2) (Circle r)]

picLine :: Float -> Float -> Vect -> Vect -> ([Picture] , Point)
picLine h r a b =
    let s = sqrt (max (h * h) (h * (fst (fst b) - fst (fst a)))) in
    let (mx , my) = picLineCoor s a b 0.5 in
    ([Line [picLineCoor s a b (t / 16) | t <- [0..16] ] , translate mx my (Circle r)] , (mx , my))

picLineCoor :: Float -> Vect -> Vect -> Float -> Point
picLineCoor h ((ax , ay) , (adx , ady)) ((bx , by) , (bdx , bdy)) t =
    (((ax + h*t*adx) * (1 + cos (pi * t)) / 2) + ((bx + h*(1-t)*bdx) * (1 - cos (pi * t)) / 2)
    ,
    ((ay + h*t*ady) * (1 + cos (pi * t)) / 2) + ((by + h*(1-t)*bdy) * (1 - cos (pi * t)) / 2)
    )

picLineCoor' :: Float -> Vect -> Vect -> Float -> Point
picLineCoor' h ((ax , ay) , (adx , ady)) ((bx , by) , (bdx , bdy)) t =
    (ax + (bx-ax) * (1 - cos (pi*t))/2
    + h * ((1-t) * adx * sin (pi*t/2) + t * bdx * cos (pi*t/2))
    ,
    ay + (by-ay) * (1 - cos (pi*t))/2
    + h * ((1-t) * ady * sin (pi*t/2) + t * bdy * cos (pi*t/2))
    )


-- =======
-- Symbols
-- =======

signPre :: Color -> Color -> Float -> Rew -> Picture
signPre _ _ _ (RI _)= Blank
signPre a b p (RS MEqual _)= pictures [
    color a (Polygon [(-p,-(2*p)) , (p,-(2*p)) , (2*p,0) , (p,2*p) , (-p,2*p) , (-(2*p),0)]) ,
    color b (Line [(-p,-(2*p)) , (p,-(2*p)) , (2*p,0) , (p,2*p) , (-p,2*p) , (-(2*p),0) , (-p,-(2*p))]) ,
    color b (Line [(-p,p) , (p,p)]) ,
    color b (Line [(-p,-p) , (p,-p)])]
signPre a b p (RS MLarger _)= pictures [
    color a (Polygon [(-p,-(2*p)) , (p,-(2*p)) , (2*p,0) , (p,2*p) , (-p,2*p) , (-(2*p),0)]) ,
    color b (Line [(-p,-(2*p)) , (p,-(2*p)) , (2*p,0) , (p,2*p) , (-p,2*p) , (-(2*p),0) , (-p,-(2*p))]) ,
    color b (Line [(p,p) , (-p,0) , (p,-p)])]
signPre a b p (RS MSmaller _)= pictures [
    color a (Polygon [(-p,-(2*p)) , (p,-(2*p)) , (2*p,0) , (p,2*p) , (-p,2*p) , (-(2*p),0)]) ,
    color b (Line [(-p,-(2*p)) , (p,-(2*p)) , (2*p,0) , (p,2*p) , (-p,2*p) , (-(2*p),0) , (-p,-(2*p))]) ,
    color b (Line [(-p,p) , (p,0) , (-p,-p)])]

mrRew :: MR -> Rew
mrRew MEqual    = RS MEqual (Start 0)
mrRew MLarger   = RS MLarger (Start 0)
mrRew MSmaller  = RS MEqual (Start 0)



-- ===================
-- =  Latex  export  =
-- ===================

-- Latex document starting code
latexPre :: String
latexPre = "\\documentclass{article}\n\n"
            ++  "\\usepackage[a4paper, total={170mm, 247mm}]{geometry}\n"
            ++  "\\usepackage{tikz}\n\n"
            ++  "\\newcommand{\\vcen}[1]{\\begingroup\\setbox0=\\hbox{#1}\\parbox{\\wd0}{\\box0}\\endgroup}\n\n"
            ++  "\\begin{document}\n"

-- Latex document ending code
latexPost :: String
latexPost = "\n\\end{document}"

-- Data type for generating Tikz pictures
data Tikz =
    TLine [Point]
    |   TPoly [Point]
    |   TText Float Point String

-- Applying a scale operation to the Tikz datatype
tikzScale :: Float -> Float -> Tikz -> Tikz
tikzScale x y (TLine l) = TLine (fmap (bimap (x *) (y *)) l)
tikzScale x y (TPoly l) = TPoly (fmap (bimap (x *) (y *)) l)
tikzScale x y (TText z (a,b) s) = TText (x*z) (x*a , y*b) s

-- Applying a translate operation to the Tikz datatype
tikzTranslate :: Float -> Float -> Tikz -> Tikz
tikzTranslate x y (TLine l) = TLine (fmap (bimap (x +) (y +)) l)
tikzTranslate x y (TPoly l) = TPoly (fmap (bimap (x +) (y +)) l)
tikzTranslate x y (TText q (a,b) s) = TText q (x+a , y+b) s

-- Generating latex code from a tikz datatype
tikzLine :: Tikz -> String
tikzLine (TLine (p : l)) = '\\' : "draw " ++ tikzPoint p ++ concatMap (\q -> " -- " ++ tikzPoint q) l ++ ";\n"
tikzLine (TPoly (p : l)) = '\\' : "draw[fill] " ++ tikzPoint p ++ concatMap (\q -> " -- " ++ tikzPoint q) l ++ " -- cycle ;\n"
tikzLine (TText q p s) = "\\draw " ++ tikzPoint p ++ " node[scale=" ++ show (q*7)  ++ "] {" ++ s ++ "};\n"
tikzLine _ = ""

-- Rounding floating numbers for reducing clutter in latex code

simpFloat :: Float -> String
simpFloat x = show (fromIntegral (round (1000*x)) / 1000)


-- Latex code for a point
tikzPoint :: Point -> String
tikzPoint (a , b) = "(" ++ simpFloat (a/80) ++ "," ++ simpFloat (-(b/80)) ++ ")"

-- Converting picture data type to list of tikz data
pictureTikz :: Picture -> [Tikz]
pictureTikz Blank = []
pictureTikz (Line l) = [TLine l]
pictureTikz (Polygon l) = [TPoly l]
pictureTikz (Scale a b p) = fmap (tikzScale a b) (pictureTikz p)
pictureTikz (Translate a b p) = fmap (tikzTranslate a b) (pictureTikz p)
pictureTikz (Text s) = [TText 1 (30,30) s]
pictureTikz (Pictures m) = concatMap pictureTikz m
pictureTikz _ = []

-- Create latex environment and code for tikzpicture of a morphism
morphTikz :: Float -> Morph -> String
morphTikz size m =  "\\vcen{\n"
            ++ "\\begin{tikzpicture}\n"
            ++ concatMap tikzLine (TLine [(0,0) , (0,size) , (size,size) , (size,0) , (0,0)]
            : pictureTikz (Pictures (pictureMorphStat size LR m)))
            ++ "\\end{tikzpicture}\n"
            ++ "}"

-- Make latex code of a Relation and its proof
allTikz :: String -> Relat -> [Rew] -> String
allTikz s x y = latexPre ++ s ++ "\n\n\\medskip\n\n" ++ relTikz x ++ "\n\n\\medskip\n\nProof:\n\n\\medskip\n\n" ++ histTikz y ++ latexPost

-- Latex code for a relation
relTikz :: Relat -> String
relTikz (MEqual     , m , n) = morphTikz 500 m ++ "\n = \n" ++ morphTikz 500 n
relTikz (MLarger    , m , n) = morphTikz 500 m ++ "\n < \n" ++ morphTikz 500 n
relTikz (MSmaller   , m , n) = morphTikz 500 m ++ "\n > \n" ++ morphTikz 500 n

-- Latex code for a proof
histTikz :: [Rew] -> String
histTikz = histTikz' 4

histTikz' :: Int -> [Rew] -> String
histTikz' _ [] = ""
histTikz' 0 l = "\n\n\\medskip\n\n" ++ histTikz l
histTikz' i (RI m : l) = morphTikz 250 m ++ histTikz' (i-1) l
histTikz' i (RS MEqual m : l) = "\n = \n" ++ morphTikz 250 m ++ histTikz' (i-1) l
histTikz' i (RS MLarger m : l) = "\n < \n" ++ morphTikz 250 m ++ histTikz' (i-1) l
histTikz' i (RS MSmaller m : l) = "\n > \n" ++ morphTikz 250 m ++ histTikz' (i-1) l

