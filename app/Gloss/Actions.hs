module Gloss.Actions where

-- standard library
import Data.Maybe
import Data.List

-- extended libraries
import Graphics.Gloss
import Graphics.Gloss.Interface.IO.Interact
import System.Directory
import Sound.ProteaAudio


-- project libraries
import Theory.Matcher
import Morph
import Theory.Rewrite
import Gloss.Display
import IO.Parse
import Theory.Theory
import Theory.Par2
import Gloss.World
import Proof
import Theory.HyperMatch
import IO.Write


-- menuing
mouseMenu :: Float -> Point -> Int
mouseMenu size (x , y) = let ty = floor (24 * y / size - 2) in
    if ty < 0 || ty > 19 then -1 else
        ty + floor (2 * x / size) * 20

menupop :: Int -> [a] -> [a]
menupop i l = menupopper (i*20) l 0

menupopper :: Int -> [a] -> Int -> [a]
menupopper _ [] _ = []
menupopper i (a : l) j
    |   i > 0       =   menupopper (i-1) l j
    |   j < 120     =   a : menupopper 0 l (j+1)
    |   otherwise   =   []



zoom :: Float
zoom = 1

playpop :: Settings -> Point -> Float -> IO ()
playpop (_ , False) _ _ = return ()
playpop _ (x , y) size = 
    let pitch = 2**(1 - (fromIntegral (round (24*y/size)) / 12))  in
    let soundPath = "guitar.mp3" in
    do
    sample <- sampleFromFile soundPath 1.0

    _ <- soundPlay sample (1-x/size) (x/size) 0.0 pitch
    putStrLn $ "Playing: " ++ soundPath

playflip :: Settings -> Float -> IO ()
playflip (_ , False) _ = return ()
playflip _ f = 
    let soundPath = "flip.mp3" in
    do
    sample <- sampleFromFile soundPath f
    _ <- soundPlay sample 0.8 0.8 0.0 1
    return ()

-- scaling all operation sizes. This makes negative sizes immune
scaleCoor :: Float -> [Coor] -> [Coor]
scaleCoor s = fmap (\(x , y , k , xyf) -> if xyf < 0 then (x , y , k , -xyf) else (x , y , k , xyf*s))

stripTxt :: String -> FilePath -> Maybe String
stripTxt [] ('.' : _) = Nothing
stripTxt [] ('/' : '.' : _) = Nothing
stripTxt [] ('/' : s) = stripTxt2 s
stripTxt [] (_ : _) = Nothing
stripTxt _ [] = Nothing
stripTxt (c : l) (d : r)
    |   c == d      =   stripTxt l r
    |   otherwise   =   Nothing


stripTxt2 :: FilePath -> Maybe String
stripTxt2 [] = Nothing
stripTxt2 ".txt" = Just ""
stripTxt2 (c : l) = fmap (c :) (stripTxt2 l)



isFolder :: String -> Bool
isFolder [] = False
isFolder ('.' : _) = False
isFolder [_] = True
isFolder (_ : l) = isFolder l

isTxt :: String -> Bool
isTxt ".txt" = True
isTxt (_ : l) = isTxt l
isTxt _ = False

recurseInput :: String -> String -> IO ([String] , [String])
recurseInput dir s
    |   isTxt s     =   if dir == "" then return ([] , [s]) else return ([] , [dir ++ "/" ++ s])
    |   isFolder s  =   (if dir == "" then listInputFile s else listInputFile (dir ++ "/" ++ s)) >>= \l -> return (l , [])
    |   otherwise   =   return ([] , [])


recurseInput' :: String -> [String] -> IO ([String] , [String])
recurseInput' _ [] = return ([] , [])
recurseInput' dir (s : l) =
    recurseInput dir s >>= \(k1 , k2) ->
    recurseInput' dir l >>= \(p1 , p2) ->
        return (k1 ++ p1 , k2 ++ p2)

listInputFile :: String -> IO [String]
listInputFile dir =
    getDirectoryContents dir >>= \l ->
    recurseInput' dir (sortSet l) >>= \(k1 , k2) ->
        return (k1 ++ k2)

    --"input"
    --fmap stripDirs (listFilesRecursive "input")

listNav :: FilePath -> IO [String]
listNav dir =
    getDirectoryContents dir >>= \l ->
    return (".." : sortSet (mapMaybe (filtNav "") l))

filtNav :: String -> String -> Maybe String
filtNav a ".txt" = Just a
filtNav _ ('.' : _) = Nothing
filtNav a "" = Just ("/" ++ a)
filtNav a (c : l) = filtNav (a ++ [c]) l

extDir :: String -> [String]
extDir = extDir' [] []

extDir' :: String -> [String] -> String -> [String]
extDir' new lis (a : '/' : l)  = extDir' "/" ((new ++ [a]) : lis) l
extDir' new lis (a : l) = extDir' (new ++ [a]) lis l
extDir' _ lis [] = lis

dirCheck :: String -> Bool
dirCheck ('/' : _) = True
dirCheck _ = False

-- going to the next page
nextState :: World -> IO World
nextState (Load size p f l i fp) = return (Load size p f l i fp)
nextState w =
    let (mode , size , ori , zom) = wmode w in
    --let law@(rel , viv , theory , future , _ , past , comment , file) = document w in
    --let (_ , _ , rlis , _) = theory in
    case mode of
        Edit {}  ->  return w
        -- normal next
        _   ->  let m = morphism w in
                let (goal , _ , (hist , i , _) , _ , _) = winfo w in
                let (rel , _ , theor , d1 , now , d2 , comment , file) = document w in
                let pagew = (rel , Just (m , i , hist , goal) , theor , d1 , now , d2 , comment , file) in
                nextPage pagew >>= \pagew' ->
                return (pageWorld size ori zom pagew' (extra w))

-- Going to the previous page
prevState :: World -> IO World
prevState (Load size p f l i fp) = return (Load size p f l i fp)
prevState w =
    let (mode , size , ori , zom) = wmode w in
    case mode of
        Edit {} -> return w
        _   ->  let m = morphism w in
                let (goal , _ , (hist , i , _) , _ , _) = winfo w in
                let (rel , _ , theor , d1 , now , d2 , comment , file) = document w in
                let pagew = (rel , Just (m , i , hist , goal) , theor , d1 , now , d2 , comment , file) in
                previousPage pagew >>= \pagew' ->
                return (pageWorld size ori zom pagew' (extra w))

editState :: World -> Relat -> [Coor] -> IO World
editState w rel loc =
    let (mode , size , ori , zom) = wmode w in
    case mode of
        Edit {} ->  let (_ , m , _ , _ , _) = rel in
                    return w {morphism = m , coordinates = loc , wmode = (Edit rel Editstart , size , ori , zom)}
        _       ->  nextState w >>= \v -> editState v rel loc

-- =================
-- Actions
-- =================

relatDisp :: Relat -> Disp
relatDisp (mr , m , n , name , why) =
        let (a , _) = typeMorph m in
        let styp = if why == Axiom then "\n\ndef  " ++ name ++ " (" else "\n\nlem  " ++ name ++ " (" in
        let mtext = morphSaveX 0 m in
        let ntext = morphSaveX 0 n in
        if why == Show then
            let rel_code = "\n\nshow  " ++ name ++ " (" ++ show a ++ ") {\n    " ++ mtext ++ "\n}" in
            Displ (mr , m , n , name , why) Nop Nothing "" True rel_code
        else
            let rel_code = styp ++ show a ++ ") {\n    " ++ mtext ++ "\n    " ++ mrSave mr : "\n    " ++ ntext ++ "\n}" in
            -- new law
            Displ (mr , m , n , name , why) Nop Nothing "" True rel_code

relatProofDisp :: Relat -> Proof -> Disp
relatProofDisp (mr , m , n , name , why) pruf =
        let (a , _) = typeMorph m in
        let styp = if why == Axiom then "\n\ndef  " ++ name ++ " (" else "\n\nlem  " ++ name ++ " (" in
        let mtext = morphSaveX 0 m in
        let ntext = morphSaveX 0 n in
        let rel_code = styp ++ show a ++ ") {\n    " ++ mtext ++ "\n    " ++ mrSave MEqual : "\n    " ++ ntext ++ "\n}" in
        let pruf_code = ("\n\n" ++ saveProof pruf) in
        -- new law
        Displ (mr , m , n , name , why)  (Yep pruf True pruf_code) Nothing "" True rel_code

-- Scrolling up action
wheelUp :: Point -> World -> IO World
wheelUp p w | isPlay w =
    let size = worldSize w in
    let (mx , my) = tM size p in
    let (goal , pap , (hist , i , f) , moder , name) = winfo w in
    let m = morphism w in
    if mx < 0 then
        if i > 0 then
            let n = sprawlProofIndex hist (i-1) in
            return w {morphism = n , coordinates = initCoor' size n , winfo = (goal , pap , (hist , i-1 , -1) , moder , name) , mouse = (mx , my)}
        else
            return w
    else if mx <= size then
        let loc = coordinates w in
        let pages = document w in
        let p' = zoomPoint size (worldZoom w) (rePoint size (getOri w) (mx , my)) in
        case rewriteNode (dewrite moder (pagePar pages)) p' (boxsize size m) m loc of
            Just (n , loc') ->  let scal = sizeMorph'' n / sizeMorph'' m in
                                return w {morphism = n , coordinates = scaleCoor scal loc' , winfo = (goal , infoNode (pagePar pages) (tM size p) (boxsize size n) n loc moder Nothing 1 , (hist , i , f) , moder , name) , mouse = tM size p}
            _               ->  let (mmod , msiz , mori , mzom) = wmode w in
                                let mmod' = Play (zoomIn (gotoZoom mmod) (rePoint size (getOri w) (mx , my)) size) in
                                return w {wmode = (mmod' , msiz , mori , mzom)}
    else return w
wheelUp p w | isEdit w = wheelUpEdit p w (wmode w)
wheelUp _ w = return w

-- Scrolling down action
wheelDown :: Point -> World -> IO World
wheelDown p w | isPlay w =
    let size = worldSize w in
    let (mx , my) = tM size p in
    let (goal , pap , (hist , i , f) , moder , name) = winfo w in
    let m = morphism w in
    if mx < 0 then
        if i < (sprawlProofLength hist - 1) then
            let n = sprawlProofIndex hist (i+1) in
            return w {morphism = n , coordinates = initCoor' size n , winfo = (goal , pap , (hist , i+1 , 1) , moder , name) , mouse = (mx , my)}
        else
            return w
    else if mx <= size then
        let loc = coordinates w in
        let pages = document w in
        let p' = zoomPoint size (worldZoom w) (rePoint size (getOri w) (mx , my)) in
        case rewriteNode (rewrite moder (pagePar pages)) p' (boxsize size m) m loc of
            Just (n , loc') ->  let scal = sizeMorph'' n / sizeMorph'' m in
                                return w {morphism = n , coordinates = scaleCoor scal loc' , winfo = (goal , infoNode (pagePar pages) (mx , my) (boxsize size n) n loc moder Nothing (-1) , (hist , i , f) , moder , name) , mouse = tM size p}
            _               ->  let (mmod , msiz , mori , mzom) = wmode w in
                                let mmod' = Play (zoomOut (gotoZoom mmod) (mx/size , my/size)) in
                                return w {wmode = (mmod' , msiz , mori , mzom)}
    else return w
wheelDown p w | isEdit w = wheelDownEdit p w (wmode w)
wheelDown _ w = return w





-- Unsafe
addId :: Int -> Int -> Float -> Float -> Float -> World -> World
addId _ w x y _ (World (Start i) loc q info mp law ext) = World (Op (Start i) w (Comp (RI (Start 1)) (Start 1))) ((x , y , True , 0) : loc) q info mp law ext
addId _ _ _ _ _ (World (Op m i o) [] q info mp law ext) = World (Op m i o) [] q info mp law ext
addId d w x y xyf (World (Op m i o) ((a , b , _ , abf) : loc) q info mp law ext)
    |   d <= 0      =   World (Op (Op m i o) w (Comp (RI (Start 1)) (Start 1))) ((x , y , False , xyf) : (a , b , False , abf) : loc) q info mp law ext
    |   otherwise   =   let ww = addId (d-1) w x y xyf (World m loc q info mp law ext) in
                            World (Op (worldMorph ww) i o) ((a , b , False , abf) : worldLoc ww) q info mp law ext
addId _ _ _ _ _ w = w

deselectNode :: [Coor] -> [Coor]
deselectNode = fmap (\(a , b , _ , abf) -> (a , b , False , abf))

clickLineCheck :: (Float , Float) -> [(Point , Int, Int)] -> Maybe (Point , Int , Int)
clickLineCheck _ [] = Nothing
clickLineCheck (mx , my) (((x , y) , i , j) : r)
    |   abs (mx-x) <= 10 && abs (my-y) <= 10    =   Just ((x , y) , i , j)
    |   otherwise                                       =   clickLineCheck (mx , my) r

-- which option in sidebar is currently being hovered over
selectOption :: Float -> Point -> Int
selectOption size (mx , my)
    |   mx <= size      =   -1
--    |   my > 0          =   -1
    |   otherwise       =   min 10 (floor (my * 24 / size - 12.1))


loadFileInit :: Float -> [String] -> (Settings , Orient , Bool) -> IO World
loadFileInit size lis ((filepath , sound) , ori , zo) =
    listNav (filepath ++ concat (reverse lis)) >>= \s ->
    return (Load size (0 , 0) lis s 0 ((filepath , sound) , ori , zo))

-- The main left-click event
clickEvent :: Point -> World -> IO World
clickEvent (mx , my) w@(World m loc (q@(Edit {}) , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) _ law ext) =
    clickEdit (mx , my) w

--_                   ->  return (World m loc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) (mx , my) law ext)
clickEvent (mx , my) (World m loc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) _ law ext)
-- right bar menu
    |   mx >= size && my > size/2 = doOption (selectOption size (mx , my)) (World m loc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) (mx , my) law ext)
    |   mx >= size && my < size/8 = let (_ , filepath , _ , _ , _) = ext in
                                    let (_ , _ , zo) = zom in
                                    let (_ , _ , _ , _ , _ , _ , _ , fn) = law in
                                    loadFileInit size (extDir fn) (filepath , ori , zo)

-- left bar history
    |   mx <= 0     =   let hn = sprawlProofLength hist in
                        let cy = round (my * 4 / size) - 1 in
                                                            -- Flip to goal
                        let w   | cy > 1 && (hi+1) >= hn    =   let n = may m (fmap sprawlGoal goal) in
                                                            let (v , ww) = transCoor m n in
                                                            let goal' = may (m , Spra []) goal in
                                                            World m loc (Tran 30 v ww n (Play zoomInit) Nothing zoomInit , size , ori , zom) (Just hist , rew , (goal' , sprawlProofLength goal' - 1 , 0) , reverseMR moder , name) (mx , my) law ext
                                                            -- Next state (by clicking next state)
                                | cy == 2               =   let (_ , _ , _ , _ , box) = sprawlNext trivPrStep (snd hist) hi in
                                                            let (m' , loc' , q') = transitionAnim size m box loc (Play zoomInit) in
                                                            World m' loc' (q' , size , ori , zom) (goal , rew , (hist , hi+1 , 1) , moder , name) (mx , my) law ext
                                                            -- Previous state (by clicking previous state)
                                | cy == 0 && hi > 0     =   let (_ , _ , _ , _ , box) = sprawlNext trivPrStep (snd hist) (hi-1) in
                                                            let (m' , loc' , q') = transitionAnim size m (reverseBox box) loc (Play zoomInit) in
                                                            World m' loc' (q' , size , ori , zom) (goal , rew , (hist , hi-1 , -1) , moder , name) (mx , my) law ext
                                                            -- Animation backwards (by clicking past previous state)
                                | cy == -1 && hi > 0    =   World m loc (Anim 10 False , size , ori , zom) (goal , rew , (hist , hi , 0) , moder , name) (mx , my) law ext
                                                            -- Animation forwards (by clicking past next state)
                                | cy == 3               =   World m loc (Anim 10 True , size , ori , zom) (goal , rew , (hist , hi , 0) , moder , name) (mx , my) law ext
                                | otherwise             =   World m loc (q , size , ori , zom) (goal , rew , (hist , hi , 0) , moder , name) (mx , my) law ext
                        in return w
-- workbench
    |   otherwise   =   let p = zoomPoint size zom (rePoint size ori (mx , my)) in
                        case clickNode p (boxsize size m) m loc of
            Just roc    ->  return (World m roc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) (mx , my) law ext)
            Nothing     ->  case clickLine p (World m loc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) (mx , my) law ext) of
                Just w  ->  return w
                Nothing ->  let n = Op m 0 (Comp (RI (Start 0)) (Start 0)) in
                            let roc = (mx , my , True , 0) : loc in
                            return (World n roc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) (mx , my) law ext)
clickEvent _ w = return w

doOption :: Int -> World -> IO World
doOption s w@(World m loc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) (mx , my) law ext@(_ , set , _ , _ , _))
    -- Open equation list
    |   s == 0  =   return (w {wmode = (Disp 0 True , size , ori , zom)})
    -- Orientation
    |   s == 1  =   return (w {wmode = (q , size , flipOrient ori , zom)})
    -- Apply autoreduction step
    |   s == 2  =   autostep2 w
    -- Zoom
    |   s == 3  =   zoomAction w
    -- Save relation
    |   s == 4  =   let (rel , _ , theory , futu , now , past , comment , file_name') = law in
                    let (_ , _ , (rews , i , _) , _ , _) = winfo w in
                    let pruf = sprawlProofUpto rews i in
                    let newrelat = extractRel (name ++ "+") Lemma (fst rews) (proofSeq pruf) MEqual in
                    let newrelat' = relatSName newrelat in
                    let disp = relatProofDisp newrelat' pruf in
                    let law' = (rel , Just (m , i , hist , goal) , theory , futu , now , disp : past , comment , file_name') in
                    let (file_name , file_code) = reconstPage law' "" in
                    previousPage law' >>= \law'' ->
                    do {putStrLn ("Saving: " ++ file_name) ;
                    writeFile file_name file_code ;
                    --writeRelat relat file_name ; 
                    return (pageWorld size ori zom law'' ext)}
    -- Split goal
    |   s == 5  =   splitLemmaDir w
    -- Old
    |   s == 6  =   return w
            --let proof = "\n\n" ++ saveProof (sprawlProofTrace hist) in
            --let file = pageFile law in
            --do { writeProof' (sprawlProofTrace hist) file ; 
            --putStrLn (snd (reconstPage law proof)) ; 
            --return w}
    -- Go to edit
    |   s == 7  =   let ((mr , _ , n , nam , why) , _ , _ , _ , _ , _ , _ , _) = law in
                    editState w (mr , m , n , nam ++ "+" , why) loc
    -- Proof stuf
    |   s == 8  =   doProof w
    -- Previous equation
    |   s == 9  =   do {playflip set 1 ; prevState w }
    -- Next equation
    |   s == 10  =  do {playflip set 1 ; nextState w}
    |   otherwise   =   return w
doOption _ w = return w


doProof :: World -> IO World
doProof w =
    let (goal , _ , (hist , i , _) , _ , _) = winfo w in
    let ((mr , m , g , name , why) , viv , theory , future , now , past , comment , file) = document w in
    let size = worldSize w in
    let coor = initCoor' size m in
    case now of
        Displ rel Nop mem comment' hid disp_code ->
            if why /= Lemma then return w else
            if proofCheck hist i goal then
                let pruf = sprawlProofUpto hist i in
                let pruf_code = ("\n\n" ++ saveProof pruf) in
                let now' = Displ rel (Yep pruf True pruf_code) mem comment' hid disp_code in
                let law' = ((mr , m , g , name , why) , viv , theory , future , now' , past , comment , file) in
                let (file_name , file_code) = reconstPage law' "" in
                do {putStrLn file_name ;
                writeFile file_name file_code ;
                return w{document = law'}}
            else return w
        Displ rel (Yep p _ _) mem comment' hid disp_code ->
            if why /= Lemma then return w else
            if proofCheck hist i goal then
                let pruf = sprawlProofUpto hist i in
                let pruf_code = ("\n\n" ++ saveProof pruf) in
                let now' = Displ rel (Yep pruf True pruf_code) mem comment' hid disp_code in
                let law' = ((mr , m , g , name , why) , viv , theory , future , now' , past , comment , file) in
                let (file_name , file_code) = reconstPage law' "" in
                do {putStrLn file_name ;
                writeFile file_name file_code ;
                return w{document = law'}}
            else
                let (mr' , m' , n' , _ , why') = proofRelat p in
                return (w{morphism = m' , coordinates = initCoor' size m' , winfo = (Just (n' , Spra []) , Nothing , (sprawlProofFromTrace p , 0 , 0) , mr' , name) ,
                    document = ((mr' , m' , n' , name , why') , viv , theory , future , now , past , comment , file)})
        _              ->  return w

-- sprawlProofFromTrace p

-- let m = startRelat rel in
--        let g = goalRelat rel in
--        let name = nameRelat rel in
--        case viv of
--            Nothing ->  let goal = if m == g then Nothing else Just (g , Spra []) in
--                        let hist = (m , Spra []) in
--                        let theory' = gatherStampAdd hist goal theory in
--                World m [(size/2,size/2,False,1) | _ <- [2..lengthMorph m]] (Play zoomInit , size , ori , zoomReset zom)
--                        (goal , Nothing , (hist , 0 , 0) , relatMR rel , name) (0 , 0) (rel , viv , theory' , future , now , past , comment , file) ext
--            Just (n , i , hist , goal) ->
--                        let theory' = gatherStampAdd hist goal theory in
--                World n [(size/2,size/2,False,1) | _ <- [2..lengthMorph n]] (Play zoomInit , size , ori , zoomReset zom)
--                        (goal , Nothing , (hist , i , 0) , relatMR rel , name) (0 , 0) (rel , viv , theory' , future , now , past , comment , file) ext

transitionAnim :: Float -> Morph -> Morph -> [Coor] -> Mode -> (Morph , [Coor] , Mode)
transitionAnim size k box coor mode =
    let m = unfoldBase k in
    let bax = unfoldPreMorph box in
    let bux = unfoldPostMorph box in
    let loc' = keepMatchCoor m bax coor in
    let (bx , by) = coorBox box (coorMorph box) in
    --let v1 = coorFilterF (boxCoorPre box) bx by zoom in 
    let v1 = boxCoorPre box in
    --let w = coorFilterF (coorMorph box) bx by zoom in 
    let w = coorMorph box in
    --let v2 = coorFilterF (boxCoorPost box) bx by zoom in 
    let v2 = boxCoorPost box in
    let (p1 , p2) = boxCoorOnly (boxsize size box) box (initCoor' size box) in
    let eff = Just (Popbox p1 p2 , 1) in
    let zom = zoomFocus (bx , by) (min 1 (sqrt (16/sizeMorph'' m))) in
    (bax , loc' , Tran 20 (coorMorph bax) (coorMorph bax) bax (Tran 20 v1 w box (Tran 20 w v2 bux mode eff zom) Nothing zom) Nothing zom)

clickLine :: (Float , Float) -> World -> Maybe World
clickLine mp (World m loc (q , size , ori , zom) info _ law ext) =
    let (_ , linfo) = pictureMorphI size ori m loc in
    clickLineCheck mp linfo >>= \((x , y) , i , j) ->
    let w = addId i j x y 0 (World m loc (q , size , ori , zom) info mp law ext) in
    Just w
clickLine _ w = return w

clickNode :: (Float , Float) -> Float -> Morph -> [Coor] -> Maybe [Coor]
clickNode (mx , my) bs (Op m _ o) ((x , y , _ , xyf) : l) = let os = sizeOper o in
    if abs (mx-x) <= bs*os && abs (my-y) <= bs*os then
        Just ((mx , my , True , xyf) : deselectNode l)
    else
        fmap ((x , y , False , xyf) :) (clickNode (mx , my) bs m l)
clickNode _ _ _ _ = Nothing

autostep :: World -> IO World
autostep (World m loc (q , size , ori , zom) (goal , x , hist , moder , name) p page ext) =
    case anyredFull size m loc (fmap fst (equivStruc (pagePar page))) of
        Just (n , _)     ->
            let (v , w) = transCoor m n in
            return (World m loc (Tran 30 v w n (Play zoomInit) Nothing zoomInit, size , ori , zom) (goal , x , hist , moder , name) p page ext)
        Nothing             ->  return (World m loc (q , size , ori , zom) (goal , x , hist , moder , name) p page ext)
autostep w = return w

autostep2 :: World -> IO World
autostep2 w =   let m = worldMorph w in
                let (_ , size , ori , zom) = wmode w in
                let page = document w in
                let par = pagePar page in
                let equ = fmap fst (equivStruc par) in
                --let redu = allredrule reduceMorph equ in 
                let redu = allredrule reduceMorph equ in -- ++ [testB , testA] in
                --let redu = [testA] in
                --case Just (testRewriteA m) of
                case hypmaRewriteAll redu m par of
                    Nothing     ->  return w
                    Just (n , x , name , w' , box)      ->
                        let loc = coordinates w in
                        let (k , loc' , mode) = transitionAnim size m box loc (Play zoomInit) in
                        return (addHistory (RS x n name w') box n (w {morphism = k , coordinates = loc' , wmode = (mode , size , ori , zom)}))
                        --return (w {morphism = n})

moveNode :: Point -> [Coor] -> [Coor]
moveNode _ [] = []
moveNode p ((x , y , False , xyf) : l)    =   (x , y , False , xyf) : moveNode p l
moveNode (mx , my) ((_ , _ , True , xyf) : l)     =   (mx , my , True , xyf) : moveNode (mx , my) l

newInfo :: Maybe (Rew , Morph , [Rew] , Float) -> Rew -> Morph -> Bool
newInfo Nothing _ _ = True
newInfo (Just (rew , mor , _ , _)) rew' mor' = rew /= rew' || mor /= mor'

infoNode :: Par Morph -> (Float , Float) -> Float -> Morph -> [Coor] -> MR
    -> Maybe (Rew , Morph , [Rew] , Float) -> Float -> Maybe (Rew , Morph , [Rew] , Float)
infoNode _ _ _ (Start _) _ _ _ _ = Nothing
infoNode _ _ _ _ [] _ _ _ = Nothing
infoNode par (mx , my) bs (Op m _ o) ((x , y , _ , _) : l) moder old f = let os = sizeOper o in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        case o of
            Comp n nh   ->  if newInfo old n nh
                            then Just (n , nh , extractRew moder n nh par , f)
                            else old
            op          ->  let n = operMorph op in
                            if newInfo old (RI n) n
                            then Just (RI n , n , extractRew moder (RI n) n par , f)
                            else old
    else
        infoNode par (mx , my) bs m l moder old f


-- rewriteNode (rewrite moder (pagePar pages)) (rePoint (getOri w) (mx , my)) (boxsize size m) m loc

-- coordinate information of box at a certain position in the sequential ordering
boxCoor :: Float -> Morph -> [Coor] -> Int -> (Point , Float)
boxCoor _ (Start _) _ _ = ((0 , 0) , 0)
boxCoor _ _ [] _ = ((0 , 0) , 0)
boxCoor s (Op m _ o) ((x , y , _ , f) : loc) j
    |   j <= 0          =   let os = s * sizeOper o * f in ((x , y) , os)
    |   otherwise       =   boxCoor s m loc (j-1)

boxCoorOnly :: Float -> Morph -> [Coor] -> (Point , Float)
boxCoorOnly _ (Start _) _ = ((0 , 0) , 0)
boxCoorOnly _ _ [] = ((0 , 0) , 0)
boxCoorOnly s (Op _ _ (Comp r n)) ((x , y , _ , f) : _) = let os = s * sizeOper (Comp r n) * f in ((x , y) , os)
boxCoorOnly s (Op m _ _) (_ : loc) = boxCoorOnly s m loc

-- the right click action
unfoldNode :: World -> (Float , Float) -> Float -> Morph -> [Coor] -> IO World
unfoldNode w p bs m lis =
    case unfoldNode' p bs m lis 0 of
        Just (rw , wm , wl , q) ->
            let scal = sizeMorph'' wm / sizeMorph'' m in
            let h1 = unfoldBaseExcept m q in
            let h2 = unfoldBase wm in
            -- effect
            let size = worldSize w in
            let (bp , bf) = boxCoor (boxsize size m) m lis q in
            let (a , set , _ , _ , _) = extra w in
            -- world 
            let w' = w {morphism = wm , coordinates = scaleCoor scal wl , extra = (a , set , Just (Popbox bp bf , 1) , Nothing , [])} in
            do {playpop set bp size ;
                --putStrLn (morphSaveX 0 m) ;
                --print h1 ; print h2 ; 
                return (addHistory rw h1 h2 w')}
        _                   ->  return w


unfoldNode' :: (Float , Float) -> Float -> Morph ->  [Coor] -> Int -> Maybe (Rew , Morph , [Coor] , Int)
unfoldNode' _ _ (Start _) _ _ = Nothing --World (Start i) r (q , size) (g , [] , hist , name) mp law
unfoldNode' _ _ _ [] _ = Nothing
unfoldNode' (mx , my) bs (Op m i (Comp n nh)) ((x , y , k , xyf) : r) q =
    let os = sizeOper (Comp n nh) in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        let n' = weakenMorph i 0 (rewMorph n) in
        let siz = 1 / sizeOper (Comp n nh) in
        Just (n , compMorph n' m , fmap (\(s , t , _ , _) -> (s + x - bs*os , t + y - bs*os , False , -siz)) (initCoor' (2*bs*os) n') ++ r , q)
    else
        unfoldNode' (mx , my) bs m r (q+1) >>= \(wr , wm , wl , q') ->
            Just (wr , Op wm i (Comp n nh) , (x , y , k , xyf) : wl , q')
--unfoldNode' (mx , my) bs (Op m i (Func "I" n)) ((x , y , k , xyf) : r) q =
--    let os = sizeOper (Func "I" n) in
--    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
--        let n' = weakenMorph i 0 n in
--        let siz = 1 / sizeOper (Func "I" n) in
--        Just (RI n , compMorph n' m , fmap (\(s , t , _ , _) -> (s + x - bs , t + y - bs , False , -siz)) (initCoor' (2*bs) n') ++ r , q)
--    else
--        unfoldNode' (mx , my) bs m r (q+1) >>= \(wr , wm , wl , q') ->
--            Just (wr , Op wm i (Func "I" n) , (x , y , k , xyf) : wl , q')
unfoldNode' (mx , my) bs (Op m i op) ((x , y , k , xyf) : r) q =
    unfoldNode' (mx , my) bs m r (q+1) >>= \(wr , wm , wl , q') ->
    Just (wr , Op wm i op , (x , y , k , xyf) : wl , q')


-- Unfold all composites into their former base
unfoldBase :: Morph -> Morph
unfoldBase (Start i)            =   Start i
unfoldBase (Op m i (Comp _ n))  =   let n' = weakenMorph i 0 n in
                                    compMorph n' (unfoldBase m)
unfoldBase (Op m i op)          =   Op (unfoldBase m) i op

unfoldBaseExcept :: Morph -> Int -> Morph
unfoldBaseExcept (Start i) _            =   Start i
unfoldBaseExcept (Op m i (Comp v n)) q
    |   q == 0      =   Op (unfoldBaseExcept m (q-1)) i (Comp v n)
    |   otherwise   =   let n' = weakenMorph i 0 n in
                        compMorph n' (unfoldBaseExcept m (q-1))
unfoldBaseExcept (Op m i (Func "I" n)) q
    |   q == 0      =  Op (unfoldBaseExcept m (q-1)) i (Comp (RS MEqual n "Id-Func" Axiom) (operMorph (Func "I" n)))
    |   otherwise   =  Op (unfoldBaseExcept m (q-1)) i (Func "I" n)
unfoldBaseExcept (Op m i op) q          =   Op (unfoldBaseExcept m (q-1)) i op

pophist :: [a] -> Maybe ([a] , a , a)
pophist [a , b] = Just ([] , a , b)
pophist (a : l) = pophist l >>= \(r , x , y) -> Just (a : r , x , y)
pophist _ = Nothing

lookHist :: Morph -> [Rew] -> Maybe Int
lookHist _ [] = Nothing
lookHist m (n : l)
    |   eqMorph m (rewMorph n)              =   Just 0
    |   otherwise                           =   fmap (1 +) (lookHist m l)

dookHist :: Int -> [Rew] -> [Rew]
dookHist _ [] = []
dookHist i (m : l)
    |   i <= 0      =   m : l
    |   otherwise   =   dookHist (i-1) l

addHistory :: Rew -> Morph -> Morph -> World -> World
addHistory (RS x _ nam w) h1 m' (World m loc q (goal , rew , ((n , hist) , hi , f) , moder , name) mp law ext) =
    let pst = (m' , x , nam , w , h1) in
    let (hist' , hi' , goal') = sprawlAddWGoal n hist hi pst goal in
        World m loc q (goal' , rew , ((n , hist') , hi' , f) , moder , name) mp law ext
--    case lookHist m' (reverse (proofSeq (n , hist))) of
--        Just i                              ->  World m loc q (g , rew , ((n , hist) , i , f) , moder , name) mp law ext
--        Nothing                             ->  World m loc q (g , rew , ((n , popList hi hist ++ [(m' , x , "?" , Axiom , h1)]) , 0 , f) , moder , name) mp law ext
addHistory _ _ _ (World m loc q (g , rew , hist , moder , name) mp law ext)  =   World m loc q (g , rew , hist , moder , name) mp law ext
addHistory _ _ _ w = w

gotoHistory :: Morph -> World -> World
gotoHistory m' (World m loc q (g , rew , ((n , hist) , hi , f) , moder , name) mp law ext) =
    --case lookHist m' (reverse (proofSeq (n , hist))) of
    case sprawlProofFind m' (n , hist) of
        Just i      ->  World m loc q (g , rew , ((n , hist) , i , f) , moder , name) mp law ext
        Nothing     ->  World m loc q (g , rew , ((n , hist) , hi , f) , moder , name) mp law ext
gotoHistory _ w = w


rightClick :: World -> (Float , Float) -> IO World
rightClick w (mx , my)
    |   isPlay w && mx < 0
                    =   let (goal , p , (hist , hi , hf) , mr , name)  = winfo w in
                        case sprawlProofToggle hist hi of
                            Just (m , hist')        ->  return w {morphism = m , coordinates = initCoor' (worldSize w) m , winfo = (goal , p , (hist' , hi , hf) , mr , name)}
                            Nothing                 ->  return w
    |   isPlay w    =   let m = morphism w in
                        let size = worldSize w in
                        let p = zoomPoint size (worldZoom w) (rePoint size (getOri w) (mx , my)) in
                        unfoldNode w p (boxsize (worldSize w) m) m (coordinates w) >>= \u ->
                        return u
    --do {putStrLn (printMorphI (worldMorph u)) ; return u}
rightClick w (mx , my) | isEdit w =
    let m = morphism w in
    let loc = coordinates w in
    let size = worldSize w in
    let bs = boxsize size m in
    let p = rePoint size (getOri w) (zoomPoint size (worldZoom w) (mx , my)) in
    let (n , roc) = deleteOp size p bs m loc in
    return (w {morphism = n , coordinates = roc})
rightClick w _ = return w

newelem :: Eq a => [a] -> [a] -> Maybe a
newelem [] _ = Nothing
newelem (a : z) s
    |   inList a s  =   newelem z s
    |   otherwise   =   Just a


-- special actions 
zoomAction :: World -> IO World
zoomAction w
    |   flatMorph (morphism w)  =   return w
    |   otherwise               =   let (relat , viv , theor , d1 , now , d2 , comment , file) = document w in
                                    let m = morphism w in
                                    let n = lastbox m m in
                                        prevState (w {document = (relat , viv , theor ,
                                            d1 , now , Displ (MEqual , n , n , "Focus" , Show) Nop Nothing "Zoomed into a part of the diagram." True "" : d2 , comment , file)})

splitLemmaDir :: World -> IO World
splitLemmaDir w =   let (relat , viv , theor , d1 , now , d2 , comment , file) = document w in
                    case relat of
                        (MEqual , m , n , name , Lemma) ->
                            let d2' = relatDisp (MLarger , m , n , name ++ "<" , Lemma) :
                                      relatDisp (MSmaller , m , n , name ++ ">" , Lemma) : d2 in
                            let law = (relat , viv , theor , d1 , now , d2' , comment , file) in
                            let w' = w {document = law} in
                            let (file_name , file_code) = reconstPage law "" in
                            do {
                            putStrLn file_name ;
                            writeFile file_name file_code ;
                            prevState w' >>= \w'' -> prevState w''
                            }
                        (MEqual , m , _ , name , Show) ->
                            let d2' = relatDisp (MLarger , m , m , name ++ "<" , Show) :
                                      relatDisp (MSmaller , m , m , name ++ ">" , Show) : d2 in
                            let law = (relat , viv , theor , d1 , now , d2' , comment , file) in
                            let w' = w {document = law} in
                            let (file_name , file_code) = reconstPage law "" in
                            do {
                            putStrLn file_name ;
                            writeFile file_name file_code ;
                            prevState w' >>= \w'' -> prevState w''}
                        _   ->  return w



newname :: [Sig] -> Maybe String
newname op = fmap (: []) (newelem "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789" (fmap (\ (Sig c _ _ _) -> popc c) op))

-- creates new operation: as composite
stampAction :: Float -> World -> IO World
stampAction bs w = --(World m loc (q , size , ori) (goal , a , hist , moder , name) mp page ext)
    let m = morphism w in
    let loc = coordinates w in
    let (_ , _ , ori , _) = wmode w in
    let mp = mouse w in
    let page = document w in
    let size = worldSize w in
    case newname (pageSig page) of
        Just c      ->  case defineOption c (rePoint size ori mp) bs m loc page 0 of
            Just  (m' , r' , page' , box , q') ->
                        return (addHistory (RS MEqual m' "" Axiom) (unfoldBaseExcept box q') (unfoldBase m') (w {morphism = m' , coordinates = r' , document = page'}))
            Nothing     ->  return w
        Nothing     ->  return w

defineOption :: String -> Point -> Float -> Morph -> [Coor] -> Page -> Int
    -> Maybe (Morph , [Coor] , Page , Morph , Int)
defineOption _ _ _ (Start _) _ _ _ = Nothing
defineOption _ _ _ _ [] _ _ = Nothing
defineOption c (mx , my) bs (Op m i (Comp rew n)) ((x , y , k , xyf) : r) (rel , v , (sig , hem , relat , par) , d1 , now , d2 , comment , file) q =
    let os = sizeOper (Comp rew n) in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        let (ni , no) = typeMorph n in
        let sig' = addSet (Sig c (Nothing ,"") ni no) sig in
        let hem' = addCompOp (Sig c (Nothing ,"") ni no) (morphOps n) hem in
        let opm = operMorph (Base (Sig c (Nothing ,"") ni no)) in
        let name = "Definition of " ++ c in
        let neweqs = (newOp hem' (Base (Sig c (Nothing ,"") ni no)) ++ [(MEqual , opm , n , name , Axiom)]) in
        let relat' =  filterAdd' neweqs relat in
        let par' = addRelatsPar neweqs par in
        let page' = (rel , v , (sig' , hem' , relat' , par') , d1 , now , d2 , comment , file) in
        Just (Op m i (Base (Sig c (Nothing ,"") ni no)) , (x , y , k , xyf) : r , page' ,
                Op m i (Comp (RS MEqual opm name Axiom) n) , q)
    else
        defineOption c (mx , my) bs m r (rel , v , (sig , hem , relat , par) , d1 , now , d2 , comment , file) (q+1) >>= \(m' , r' , page' , box , q') ->
        Just (Op m' i (Comp rew n) , (x , y , k , xyf) : r' , page' , Op box i (Comp rew n) , q')
defineOption c mp bs (Op m i op) ((x , y , k , xyf) : r) law q =
    defineOption c mp bs m r law (q+1) >>= \(m' , r' , law' , box , q') ->
    Just (Op m' i op , (x , y , k , xyf) : r' , law' , Op box i op , q')


-- creates new operation: as composite, but it is stored directly
stampActionF :: Float -> World -> IO World
stampActionF bs w = --(World m loc (q , size , ori) (goal , a , hist , moder , name) mp page ext)
    let m = morphism w in
    let loc = coordinates w in
    let (_ , _ , ori , _) = wmode w in
    let mp = mouse w in
    let page = document w in
    let size = worldSize w in
    case defineOptionF (rePoint size ori mp) bs m loc page 0 of
        Just  (m' , r' , page' , box , q') ->
                        do {print page' ; return (addHistory (RS MEqual m' "F(I)" Axiom) (unfoldBaseExcept box q') (unfoldBase m') (w {morphism = m' , coordinates = r' , document = page'}))}
        Nothing     ->  return w


defineOptionF :: Point -> Float -> Morph -> [Coor] -> Page -> Int
    -> Maybe (Morph , [Coor] , Page , Morph , Int)
defineOptionF _ _ (Start _) _ _ _ = Nothing
defineOptionF _ _ _ [] _ _ = Nothing
defineOptionF (mx , my) bs (Op m i (Comp rew n)) ((x , y , k , xyf) : r) (rel , v , theor , d1 , now , d2 , comment , file) q =
    let os = sizeOper (Comp rew n) in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        let opm = operMorph (Func "I" n) in
        let page' = (rel , v , defineStampF n theor , d1 , now , d2 , comment , file) in
        Just (Op m i (Func "I" n) , (x , y , k , xyf) : r , page' ,
                Op m i (Comp (RS MEqual opm "Id-Func" Axiom) n) , q)
    else
        defineOptionF (mx , my) bs m r (rel , v , theor , d1 , now , d2 , comment , file) (q+1) >>= \(m' , r' , page' , box , q') ->
        Just (Op m' i (Comp rew n) , (x , y , k , xyf) : r' , page' , Op box i (Comp rew n) , q')
defineOptionF mp bs (Op m i op) ((x , y , k , xyf) : r) law q =
    defineOptionF mp bs m r law (q+1) >>= \(m' , r' , law' , box , q') ->
    Just (Op m' i op , (x , y , k , xyf) : r' , law' , Op box i op , q')

-- Adding rules for the stamp of a morphism
defineStampF :: Morph -> Theor -> Theor
defineStampF n (sig , hem , relat , par) =
    let opm = operMorph (Func "I" n) in
    let neweqs = (newOp hem (Func "I" n) ++ [(MEqual , opm , n , "Id-Func" , Axiom)]) in
    let relat' =  filterAdd' neweqs relat in
    let par' = addRelatsPar neweqs par in
    (sig , hem , relat' , par')


-- gathering all stamps used, to add to theory when navigating pages
gatherStampMorph :: [Morph] -> Morph -> [Morph]
gatherStampMorph gat (Start _) = gat
gatherStampMorph gat (Op m _ (Func "I" n)) = gatherStampMorph (addSet n gat) m
gatherStampMorph gat (Op m _ _) = gatherStampMorph gat m

gatherStampSprawl :: [Morph] -> Sprawl -> [Morph]
gatherStampSprawl gat (Spra []) = gat
gatherStampSprawl gat (Spra (((m , _ , _ , _ , _) , s) : l)) = gatherStampSprawl (gatherStampSprawl (gatherStampMorph gat m) s) (Spra l)

gatherStampHist :: SprawlProof -> Maybe SprawlProof -> [Morph]
gatherStampHist (m , s) Nothing = gatherStampSprawl (gatherStampMorph [] m) s
gatherStampHist (m , s) (Just (n , z)) = gatherStampSprawl (gatherStampMorph (gatherStampSprawl (gatherStampMorph [] m) s) n) z

gatherStampAdd :: SprawlProof -> Maybe SprawlProof -> Theor -> Theor
gatherStampAdd hist goal t = foldl (flip defineStampF) t (gatherStampHist hist goal)

-- Adding currently proven relation to relations
addCurrentRel :: World -> (World , Relat)
addCurrentRel (Load x y f z w fp) = (Load x y f z w fp , (MEqual , Start 0 , Start 0 , "" , Show))
addCurrentRel w =
    let (_ , _ , (rews , _ , _) , _ , name) = winfo w in
    let newrelat = extractRel (name ++ "+") Lemma (fst rews) (proofSeq (sprawlProofTrace rews)) MEqual in
    let (rel , v , (sigs , schem , relat , par) , d1 , now , d2 , comment , file) = document w in
    let relats = newrelat : newRelats schem [newrelat] in
    let theor' = (sigs , schem , filterAdd' relats relat , addRelatsPar relats par) in
        (w {document = (rel , v , theor' , d1 , now , Assum newrelat "" : d2 , comment , file)} , newrelat)


extractRel :: String -> Why -> Morph -> [Rew] -> MR -> Relat
extractRel name w m [] _ = (MEqual , m , m , name , w)
extractRel name w m [RI n] y = (y , m , n , name , w)
extractRel name w m [RS x n _ _] y = (joinMRunsafe x y , m , n , name , w)
extractRel name w m ((RI _) : l) y = extractRel name w m l y
extractRel name w m ((RS x _ _ _) : l) y = extractRel name w m l (joinMRunsafe x y)


deleteOp :: Float -> Point -> Float -> Morph -> [Coor] -> (Morph , [Coor])
deleteOp size (mx , my) bs (Op m i op) ((x , y , b , xyf) : loc)
    |   abs (mx - x) <= bs && abs (my - y) <= bs    =   (m , loc)
    |   otherwise                                   =
            let (n , roc) = deleteOp size (mx , my) bs m loc in
            let (_ , no) = typeMorph n in
            let (opi , _) = typeOper op in
            if opi <= no
            then (Op n (min i (no-opi)) op , (x , y , b , xyf) : roc)
            else (Op m i op , (x , y , b , xyf) : loc)
deleteOp _ _ _ m loc = (m , loc)



-- ===================================
-- ==   R E S T R U C T U R I N G   ==
-- ===================================


-- Loading world from page
pageWorld :: Float -> Orient -> Zoom -> Page -> Extra -> World
pageWorld size ori zom (rel , viv , theory , future , now , past , comment , file) ext
    |   isEnd rel   =   World (Start 1) [] (initEdit , size , ori , zoomReset zom)
                                (Nothing , Nothing , ((Start 1 , Spra []) , 0 , 0) , MLarger , "Editor" ) (0 , 0)
                                ((MEqual , Start 1 , Start 1 , "Editor" , Axiom) , Nothing , theory , future , now , past , comment , file) ext
    |   otherwise   =
        let m = startRelat rel in
        let g = goalRelat rel in
        let name = nameRelat rel in
        case viv of
            Nothing ->  let goal = if m == g then Nothing else Just (g , Spra []) in
                        let hist = (m , Spra []) in
                        let theory' = gatherStampAdd hist goal theory in
                World m [(size/2,size/2,False,1) | _ <- [2..lengthMorph m]] (Play zoomInit , size , ori , zoomReset zom)
                        (goal , Nothing , (hist , 0 , 0) , relatMR rel , name) (0 , 0) (rel , viv , theory' , future , now , past , comment , file) ext
            Just (n , i , hist , goal) ->
                        let theory' = gatherStampAdd hist goal theory in
                World n [(size/2,size/2,False,1) | _ <- [2..lengthMorph n]] (Play zoomInit , size , ori , zoomReset zom)
                        (goal , Nothing , (hist , i , 0) , relatMR rel , name) (0 , 0) (rel , viv , theory' , future , now , past , comment , file) ext

selectMenu :: Bool -> Int -> [String] -> World -> IO World
selectMenu b i (a : l) (Load size p f r j ((fa , fm) , fb , fc))
    |   i >= 40     =   return (Load size p f r (j+1) ((fa , fm) , fb , fc))
    |   i < 0       =   return (Load size p f r (max 0 (j-1)) ((fa , fm) , fb , fc))
    |   i > 0       =   selectMenu b (i-1) l (Load size p f r j ((fa , fm) , fb , fc))
    |   a == ".."   =   loadFileInit size (tailList f) ((fa , fm) , fb , fc)
    |   dirCheck a  =   loadFileInit size (a : f) ((fa , fm) , fb , fc)
    |   otherwise   =   let filep = (concat (reverse f) ++ "/" ++ a) in 
                        initPage b filep fa >>= \pp ->
                        case pp of
                            Just page   -> return (pageWorld size fb (zoomSet fc) page ((0 , []) , (fa , fm)  , Nothing , Nothing , []))
                            Nothing     -> return (Load size p f r j ((fa , fm) , fb , fc))
selectMenu b i [] (Load size p f r j fp)
    |   i < 0       =   return (Load size p f r (max 0 (j-1)) fp)
    |   otherwise   =   return (Load size p f r j fp)
selectMenu _ _ _ w = return w


-- set lemma
setRelatWorld :: Wtyp -> Relat -> World -> IO World
setRelatWorld wty relat w =
    let (currel , mem , theor , disp1 , _ , disp2 , comment , file) = document w in
    case disp2 of
        (now' : disp2') ->  let disp1' =    if wty == WDef then Assum relat "" : Displ relat Nop Nothing "" True "" : disp1
                                            else Displ relat Nop Nothing "" True "" : Assum relat "" : disp1  in
                                            nextPage (currel , mem , theor , disp1' , now' , disp2' , comment , file) >>= \page ->
                                            return (pageWorld (worldSize w) (worldOrient w) (worldZoom w) page (worldExtra w))
        _               ->  return w

setOperWorld :: Sig -> World -> IO World
setOperWorld op w =
    let (currel , mem , theor , disp1 , _ , disp2 , comment , file) = document w in
    case disp2 of
        (now' : disp2') ->  let disp1' = Opera op "" : disp1 in
                            nextPage (currel , mem , theor , disp1' , now' , disp2' , comment , file) >>= \page ->
                            return (pageWorld (worldSize w) (worldOrient w) (worldZoom w) page (worldExtra w))
        _               ->  return w



-- ===================================
-- === E D I T   W O R K B E N C H ===
-- ===================================

quickMY :: Float -> Float -> Int
quickMY size my = floor (my*24/size)

-- Click action
-- o On right sidebar, clicking options
-- o On workbench, manipulating diagram
-- o On left sidebard, adding operation
clickEdit :: Point -> World -> IO World
clickEdit (mx , my) w@(World m loc (q@(Edit rel@(mr , st , go , nam , why) mo) , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) _ law ext)
    |   mx <= 0     =   let w = World m loc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) (mx , my) law ext in
                        let (_ , _ , (oper , _ , _ , _) , _ , _ , _ , _ , _) = law in
                        let s = round (20*my/size)-1 in
                        case lookupList s oper of
                            Just op     ->  return (w {morphism = addOper op m , coordinates = (size/2 , size/2 , False , 1) : loc})
                            _           ->  return w
    |   mx < size   =   let p = zoomPoint size zom (rePoint size ori (mx , my)) in
                        case clickNode p (boxsize size m) m loc of
            Just roc    ->  return (World m roc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) (mx , my) law ext)
            Nothing     ->  case clickLine p (World m loc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) (mx , my) law ext) of
                Just w  ->  return w
                Nothing ->  let n = Op m 0 (Comp (RI (Start 0)) (Start 0)) in
                            let roc = (mx , my , True , 0) : loc in
                            return (World n roc (q , size , ori , zom) (goal , rew , (hist , hi , f) , moder , name) (mx , my) law ext)
-- Load file: backing out of file and going back to start-up screen
    |   quickMY size my <= 2
                    =   let (_ , filepath , _ , _ , _) = ext in
                        let (_ , _ , zo) = zom in
                        loadFileInit size [] (filepath , ori , zo)
-- Rename relation: Will go to editname mode, in which new name can be typed
    |   quickMY size my <= 4
                    =   return (w{wmode = (Edit (mr , st , go , nam , why) Editname , size , ori , zom)})
-- Change between Lemma and Axiom
    |   quickMY size my <= 5
                    =   return (w{wmode = (Edit (mr , st , go , nam , toggleWhy why) mo , size , ori , zom)})
-- Shift to editting the starting state of the relation, left/top side.
    |   quickMY size my <= 11
                    =   return w{morphism = st , coordinates = initCoor' size st , wmode = (Edit (mr , st , go , nam , why) Editstart , size , ori , zom)}
-- Shift to editting the goal state of the relation, right/bottom side.
    |   quickMY size my <= 17
                    =   return w{morphism = go , coordinates = initCoor' size go , wmode = (Edit (mr , st , go , nam , why) Editgoal , size , ori , zom)}
-- Change type of relation: equation, smaller-equal, larger-equal
    |   quickMY size my <= 18
                    =   return (w{wmode = (Edit (toggleMR mr , st , go , nam , why) mo , size , ori , zom)})
-- Finish and add relation to end of file, opening it in standard Play mode.
    |   quickMY size my <= 19
                    =   if relatCheck rel then
                            let disp = relatDisp rel in
                            let (_ , _ , theory , future , _ , past , comment , file) = law in
                            let law' = (rel , Nothing , theory , future , disp , past , comment , file) in
                            let (file_name , file_code) = reconstPage law' "" in
                            do {putStrLn file_name ;
                                writeFile file_name file_code ;
                                return (pageWorld (worldSize w) (worldOrient w) (worldZoom w) law' (worldExtra w))}
                else
                    return w
-- Initialize (or cancel) adding a new operation
    |   quickMY size my <= 20
                    =   case mo of
                            Editoper sig@(Sig c (_ , y) a b)  ->  case findMorph (pageSig (document w)) c of
                                Just _      ->   return w
                                Nothing     ->
                                    let (_ , _ , theory , futu , _ , past , _ , file) = document w in
                                    let op_code = "\n\nop  " ++ c ++ " : " ++ show a ++ " -> " ++ show b ++ if y == "" then "" else " [" ++ y ++ "]" in
                                    let now = Opera sig op_code in
                                    newSteps' theory (now : futu) past file >>= \law' ->
                                    let (file_name , file_code) = reconstPage law' "" in
                                    do {writeFile file_name file_code ;
                                        return (w { morphism = st , coordinates = initCoor' size st ,
                                                    wmode = (Edit rel Editstart , size , ori , zom) , document = law'})}
                            _   ->  let (_ , _ , (sig , _ , _ , _) , _ , _ , _ , _ , _) = law in
                                    case newChar sig of
                                Just c      ->  let op = Sig [c] (Nothing , "") 2 2 in
                                            return (w {wmode = (Edit rel (Editoper op) , size , ori , zom)})
                                Nothing     ->  return w
-- Backing out of edit mode, going back to last Page
    |   otherwise
                    =   previousPage law >>= \law' -> return (pageWorld (worldSize w) (worldOrient w) (worldZoom w) law' (worldExtra w))
clickEdit _ w = return w


-- Right click action
-- o On workbench, remove operation



-- Scroll action
-- o In relation start/goal editing mode:
-- ----o Hovering over morphism being edited: will add or remove strings
-- ----o Hovering over operation sidebar on left, will scroll through operations
-- ----o Extra: hovering over start/goal, will change into alt options
-- o In operation editing mode:
-- ----o Add or remove input or output wire, depending on third
-- ----o Scroll through drawing styles when in middle
wheelUpEdit :: Point -> World -> (Mode , Float , Orient , Zoom) -> IO World
wheelUpEdit (mx , my) w (Edit rel (Editoper (Sig nam (k , r) a b)) , size , ori , zom)
    |   mx <= (-(size/2))   =   return w
    |   mx <= (-(size/6))   =   return (w {wmode = (Edit rel (Editoper (Sig nam (k , r) (max 0 (a-1)) b)) , size , ori , zom) })
    |   mx <= (size/6)      =   return (w {wmode = (Edit rel (Editoper (Sig nam (k , listTogUp r styleList) a b)) , size , ori , zom) })
    |   mx <= (size/2)      =   return (w {wmode = (Edit rel (Editoper (Sig nam (k , r) a (max 0 (b-1)))) , size , ori , zom) })
    |   otherwise           =   return w
wheelUpEdit _ w (Edit {} , size , ori , zom) = return (w { morphism = removeWire (morphism w)})
wheelUpEdit _ w _ = return w

wheelDownEdit :: Point -> World -> (Mode , Float , Orient , Zoom) -> IO World
wheelDownEdit (mx , my) w (Edit rel (Editoper (Sig nam (k , r) a b)) , size , ori , zom)
    |   mx <= (-(size/2))   =   return w
    |   mx <= (-(size/6))   =   return (w {wmode = (Edit rel (Editoper (Sig nam (k , r) (a + 1) b)) , size , ori , zom) })
    |   mx <= (size/6)      =   return (w {wmode = (Edit rel (Editoper (Sig nam (k , listTogDown r styleList) a b)) , size , ori , zom) })
    |   mx <= (size/2)      =   return (w {wmode = (Edit rel (Editoper (Sig nam (k , r) a (b + 1))) , size , ori , zom) })
    |   otherwise           =   return w
wheelDownEdit _ w (Edit {} , size , ori , zom) = return (w { morphism = extraWire (morphism w)})
wheelDownEdit _ w _ = return w

-- Press character action
-- o In relation start/goal editing mode, it will add an operation to morphism being edited
-- o In relation name editing mode, it will edit the name
-- o In operation generation mode, it will type name
editorAddChar :: String -> KeyState -> World -> Mode -> IO World
editorAddChar c ct w (Edit (mr , start , goal , name , why) (Editoper (Sig char style l writ))) =
    case findMorph (pageSig (document w)) c of
        Just _      ->  return w
        _           ->  let (_ , size , ori , zom) = wmode w in
                        let mode = (Edit (mr , start , goal , name , why) (Editoper (Sig c style l writ)) , size , ori , zom) in
                        return w{wmode = mode}
editorAddChar (c : _) ct w (Edit (mr , start , goal , name , why) Editname) =
    let (_ , size , ori , zom) = wmode w in
    let name' = nameUpdate name c in
    return w{wmode = (Edit (mr , start , goal , name' , why) Editname , size , ori , zom)}
editorAddChar c ct w (Edit (mr , start , goal , name , why) writ) =
        let m = morphism w in
        let (_ , size , ori , zom) = wmode w in
        case findMorph (pageSig (document w)) c of
        Just (Sig d s i j)  ->  let m' = addOper (Sig d s i j) m in
                                let mode = if writ == Editstart then Edit (mr , m' , goal , name , why) writ else Edit (mr , start , m' , name , why) writ in
                                return (w {morphism = m' , coordinates = initCoor' size m', wmode = (mode , size , ori , zom)})
        Nothing             ->  return (w {wmode = (Edit (mr , start , goal , name , why) (Editoper (Sig c blankStyle 2 2)) , size , ori , zom)})
editorAddChar _ _ w _ = return w


editBackspace :: World -> IO World
editBackspace w@(World m loc (Edit _ Editstart , _ , _ , _) _ _ _ _)
    =   return (w {morphism = removeLast m , coordinates = tailList loc})
editBackspace w@(World m loc (Edit _ Editgoal , _ , _ , _) _ _ _ _)
    =   return (w {morphism = removeLast m , coordinates = tailList loc})
editBackspace w@(World _ _ (Edit (mr , st , go , nam , why) Editname , size , ori , zom) _ _ _ _)
    =   return (w {wmode = (Edit (mr , st , go , nameBack nam , why)  Editname , size , ori , zom)})
editBackspace w = return w

nameUpdate :: String -> Char -> String
nameUpdate [] ' ' = []
nameUpdate [_] ' ' = []
nameUpdate (c : l) ' ' = c : nameUpdate l ' '
nameUpdate s c
    |   inList c "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789=<>-+*!?_"
                    =   s ++ [c]
    |   otherwise   =   s

nameBack :: String -> String
nameBack [] = []
nameBack [_] = []
nameBack (c : l) = c : nameBack l

sigChars :: [Sig] -> String
sigChars [] = []
sigChars (Sig [c] _ _ _ : l) = c : sigChars l
sigChars (_ : l) = sigChars l

newChar :: [Sig] -> Maybe Char
newChar sig = newChar' "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ" (sortSet (sigChars sig))

newChar' :: String -> String -> Maybe Char
newChar' [] _ = Nothing
newChar' (c : l) s
    |   inSet c s   =   newChar' l s
    |   otherwise   =   Just c


listTogUp :: Eq a => a -> [a] -> a
listTogUp a [] = a
listTogUp a (b : l) = listTogUp' a b (b : l)

listTogUp' :: Eq a => a -> a -> [a] -> a
listTogUp' _ b [] = b
listTogUp' _ b [_] = b
listTogUp' a b (c : d : l)
    |   a == c      =   d
    |   otherwise   =   listTogUp' a b (d : l)


listTogDown :: Eq a => a -> [a] -> a
listTogDown a [] = a
listTogDown a (b : l)
    |   a == b      =   lastL a l
    |   otherwise   =   listTogDown' a (b : l)

listTogDown' :: Eq a => a -> [a] -> a
listTogDown' a [] = a
listTogDown' _ [b] = b
listTogDown' a (b : c : l)
    |   a == c      =   b
    |   otherwise   =   listTogDown' a (c : l)

-- old previous in edit
                -- (WRel wty (Just m)) ->
        --     let loc = initCoor' size m in
        --     return (w {morphism = m , coordinates = loc , wmode = (Edit (WRel wty Nothing) , size , ori , zoomReset zom)})
        -- Edit (WOpe _ _ r) ->
        --     return (w {wmode = (Edit r , size , ori , zoomReset zom)})