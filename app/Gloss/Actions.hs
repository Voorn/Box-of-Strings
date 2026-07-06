module Gloss.Actions where 

-- standard library
import Data.Maybe
import Data.List

-- extended libraries
import Graphics.Gloss
import Graphics.Gloss.Interface.IO.Interact
import System.Directory

-- project libraries
import Matcher
import Morph
import Rewrite
import Gloss.Display
import Parse
import Theory
import Par2
import Gloss.World
import Proof
import HyperMatch
import Write


stripTxt :: FilePath -> Maybe String
stripTxt [] = Nothing
stripTxt ".txt" = Just ""
stripTxt (c : l) = fmap (c :) (stripTxt l)

stripDir :: String -> Maybe String 
stripDir ('i' : 'n' : 'p' : 'u' : 't' : '/' : '.' : _) = Nothing 
stripDir ('i' : 'n' : 'p' : 'u' : 't' : '/' : l) = Just l 
stripDir _ = Nothing

stripDirs :: [String] -> [String]
stripDirs [] = []
stripDirs (s : l) = case stripDir s of 
    Just z      ->  z : stripDirs l 
    Nothing     ->  stripDirs l

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

listInputFiles :: IO [String]
listInputFiles = listInputFile ""

listInputFile :: String -> IO [String]
listInputFile dir = 
    getDirectoryContents ("input" ++ "/" ++ dir) >>= \l -> 
    recurseInput' dir (sortSet l) >>= \(k1 , k2) ->
        return (k1 ++ k2)

    --"input"
    --fmap stripDirs (listFilesRecursive "input")

nextState :: World -> IO World
nextState (Load size p l) = return (Load size p l)
nextState w =
    let (mode , size , ori) = wmode w in
    case mode of 
        Edit (WRel wty Nothing)  
            ->  let (a , _) = typeMorph (worldMorph w) in 
                return (w {wmode = (Edit (WRel wty (Just (worldMorph w))) , size , ori)})
        Edit (WRel wty (Just m))
            ->  let n = worldMorph w in 
                if typeMatch m n then
                    let (_ , _ , _ , _ , _ , _ , file) = document w in
                    do {writeLemma wty file m n; 
                    return (setRelatWorld wty (MEqual , m , worldMorph w , "Unnamed" , wtypWhy wty) w)}
                else 
                    return w
        -- normal next
        _   ->  let m = morphism w in
                let (goal , _ , (hist , i) , _ , _) = winfo w in
                let (rel , _ , theor , d1 , d2 , comment , file) = document w in
                let pagew = (rel , Just (m , i , hist , goal) , theor , d1 , d2 , comment , file) in
                return (pageWorld size ori (nextPage pagew) (extra w))

prevState :: World -> IO World
prevState (Load size p l) = return (Load size p l)
prevState w =
    let (mode , size , ori) = wmode w in
    case mode of
        Edit (WRel wty (Just m)) -> 
            let loc = initCoor' size m in
            return (w {morphism = m , coordinates = loc , wmode = (Edit (WRel wty Nothing) , size , ori)})  
        Edit (WOpe _ _ r) -> 
            return (w {wmode = (Edit r , size , ori)})  
        _   ->  let m = morphism w in
                let (goal , _ , (hist , i) , _ , _) = winfo w in
                let (rel , _ , theor , d1 , d2 , comment , file) = document w in
                let pagew = (rel , Just (m , i , hist , goal) , theor , d1 , d2 , comment , file) in
                return (pageWorld size ori (previousPage pagew) (extra w))

-- =================
-- Actions
-- =================
wheelUp :: Point -> World -> IO World 
wheelUp p w | isPlay w = 
    let size = worldSize w in
    let (mx , my) = tM size p in
    let (goal , pap , (hist , i) , moder , name) = winfo w in
    let m = morphism w in
    if mx < 0 then 
        if i < (lengthProof hist - 1) then 
            let n = rewMorph (lookList (i+1) (RI m) (proofSeq hist)) in 
            return w {morphism = n , coordinates = initCoor' size n , winfo = (goal , pap , (hist , i+1) , moder , name) , mouse = (mx , my)}
        else 
            return w
    else 
        let loc = coordinates w in
        let pages = document w in
        let n = rewriteNode (rewrite moder (pagePar pages)) (rePoint size (getOri w) (mx , my)) (boxsize size m) m loc in
        return w {morphism = n , winfo = (goal , infoNode (pagePar pages) (mx , my) (boxsize size n) n loc moder Nothing, (hist , i) , moder , name) , mouse = tM size p}
wheelUp _ w | isEdit w = return (w { morphism = removeWire (morphism w)})
wheelUp _ w = return w

wheelDown :: Point -> World -> IO World 
wheelDown p w | isPlay w = 
    let size = worldSize w in
    let (mx , my) = tM size p in
    let (goal , pap , (hist , i) , moder , name) = winfo w in
    let m = morphism w in
    if mx < 0 then 
        if i > 0 then 
            let n = rewMorph (lookList (i-1) (RI m) (proofSeq hist)) in 
            return w {morphism = n , coordinates = initCoor' size n , winfo = (goal , pap , (hist , i-1) , moder , name) , mouse = (mx , my)}
        else 
            return w
    else 
        let loc = coordinates w in
        let page = document w in
        let n = rewriteNode (dewrite moder (pagePar page)) (rePoint size (getOri w) (tM size p)) (boxsize size m) m loc in
        return w {morphism = n , winfo = (goal , infoNode (pagePar page) (tM size p) (boxsize size n) n loc moder Nothing , (hist , i) , moder , name) , mouse = tM size p}
wheelDown _ w | isEdit w = return (w { morphism = extraWire (morphism w)})
wheelDown _ w = return w 


-- Editor character
editorAddChar :: Char -> KeyState -> World -> Writ -> IO World
editorAddChar _ _ (Load x y z) _ = return (Load x y z)
editorAddChar c ct w (WRel k wty) =
        let m = morphism w in
        let (_ , size , ori) = wmode w in
        let loc = coordinates w in
        case findMorph (pageSig (document w)) c of
        Just (Sig d s i j)  ->  return (w {morphism = addOper (Sig d s i j) m , coordinates = (size/2 , size/2 , False) : loc})
        Nothing             ->  return (w {wmode = (Edit (WOpe c Nothing (WRel k wty)) , size , ori)})
editorAddChar c ct w (WOpe char l writ) = 
        let (_ , size , ori) = wmode w in
        case numParse' c of
            Just k      ->  case l of 
                Nothing ->  return (w {wmode = (Edit (WOpe char (Just k) writ) , size , ori)})
                Just a  ->  let sig = Sig char (Nothing , "") a k in 
                            let (_ , _ , _ , _ , _ , _ , file) = document w in
                            do {writeOperation file sig ;
                            return (setOperWorld (Sig char (Nothing , "") a k) w)}
            _           ->  return w


-- Unsafe
addId :: Int -> Int -> Float -> Float -> World -> World
addId _ w x y (World (Start i) loc q info mp law ext) = World (Op (Start i) w (Comp (RI (Start 1)) (Start 1))) ((x , y , True) : loc) q info mp law ext
addId _ _ _ _ (World (Op m i o) [] q info mp law ext) = World (Op m i o) [] q info mp law ext
addId d w x y (World (Op m i o) ((a , b , _) : loc) q info mp law ext)
    |   d <= 0      =   World (Op (Op m i o) w (Comp (RI (Start 1)) (Start 1))) ((x , y , False) : (a , b , False) : loc) q info mp law ext
    |   otherwise   =   let ww = addId (d-1) w x y (World m loc q info mp law ext) in
                            World (Op (worldMorph ww) i o) ((a , b , False) : worldLoc ww) q info mp law ext
addId _ _ _ _ w = w

deselectNode :: [(Float , Float , Bool)] -> [(Float , Float , Bool)]
deselectNode = fmap (\(a , b , _) -> (a , b , False))

clickLineCheck :: (Float , Float) -> [(Point , Int, Int)] -> Maybe (Point , Int , Int)
clickLineCheck _ [] = Nothing
clickLineCheck (mx , my) (((x , y) , i , j) : r)
    |   abs (mx-x) <= 10 && abs (my-y) <= 10    =   Just ((x , y) , i , j)
    |   otherwise                                       =   clickLineCheck (mx , my) r

clickEvent :: (Float , Float) -> World -> IO World
clickEvent (mx , my) (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) _ law ext)
-- right bar menu
    -- Open equation list
    |   mx >= size && my <= size*0.125
                    =   return (World m loc (Disp 0 , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext)
    -- Load file 
    |   mx >= size && my <= size*0.25
                    =   listInputFiles >>= \s ->
                        return (Load size (mx , my) (mapMaybe stripTxt s))
    -- Previous / Next equation
    |   mx >= (size * 9/8) && my >= size*0.875
                    =   nextState (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext)
    |   mx >= size && my >= size*0.875
                    =   prevState (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext)
    -- Flip
    |   mx >= (size * 9/8) && my >= size*3/4
                    =   return (World m loc (q , size , flipOrient ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext)
    -- Apply autoreduction step
    |   mx >= size && my >= size*0.75
                    =   autostep2 (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext)
    -- Save relation
    |   mx >= (size * 9/8) && my >= size*5/8
                    =   return (addCurrentRel (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext))
    -- Zoom
    |   mx >= size && my >= size*5/8
                    =   zoomAction (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext)
    |   mx >= size  =   case q  of 
            Edit (WRel wty z)   ->  return (World m loc (Edit (WRel (toggleWtyp wty) z) , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext)
            _                   ->  return (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext)
-- left bar history
    |   mx <= 0     =   case q of 
            Edit (WRel _ _) ->  
                        let w = World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext in
                        let (_ , _ , (oper , _ , _ , _) , _ , _ , _ , _) = law in
                        let s = round(20*my/size)-1 in 
                        case lookupList s oper of 
                            Just op     ->  return (w {morphism = addOper op m , coordinates = (size/2 , size/2 , False) : loc})
                            _           ->  return w
            _       ->  let hn = lengthProof hist in
                        let cy = round (my * 4 / size) - 1 in
                        let w   | cy > 1 && hi <= 0     =   let n = looku 0 m (fmap rewMorph (proofSeqM goal)) in
                                                            let (v , w) = transCoor m n in
                                                            World m loc (Tran 30 v w n Play , size , ori) (Just hist , rew , (proofM goal , 0) , reverseMR moder , name) (mx , my) law ext
                                | cy == 2               =   let (_ , _ , _ , _ , box) = looku (hn-hi-1) (m , MEqual , "" , Axiom , m) (snd hist) in
                                                            let (m' , loc' , q') = transitionAnim m box loc Play in
                                                            World m' loc' (q' , size , ori) (goal , rew , (hist , hi-1) , moder , name) (mx , my) law ext
                                | cy == 0 && (hi + 1) < hn  =   let (_ , _ , _ , _ , box) = looku (hn-hi-2) (m , MEqual , "" , Axiom , m) (snd hist) in
                                                            let (m' , loc' , q') = transitionAnim m (reverseBox box) loc Play in
                                                            World m' loc' (q' , size , ori) (goal , rew , (hist , hi+1) , moder , name) (mx , my) law ext
                                | cy == -1 && (hi + 1) < hn  = World m loc (Anim 10 False , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext
                                | cy == 3               =   World m loc (Anim 10 True , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext
                                | otherwise             =   World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext
                        in return w
-- workbench
    |   otherwise   =   case clickNode (rePoint size ori (mx , my)) (boxsize size m) m loc of
            Just roc    ->  return (World m roc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext)
            Nothing     ->  case clickLine (rePoint size ori (mx , my)) (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext) of
                Just w  ->  return w
                Nothing ->  let n = Op m 0 (Comp (RI (Start 0)) (Start 0)) in 
                            let roc = (mx , my , True) : loc in  
                            return (World n roc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law ext)
clickEvent _ w = return w

transitionAnim :: Morph -> Morph -> [(Float , Float , Bool)] -> Mode -> (Morph , [(Float , Float , Bool)] , Mode)
transitionAnim k box coor mode = 
    let m = unfoldBase k in
    let bax = unfoldPreMorph box in 
    let bux = unfoldPostMorph box in 
    let loc' = keepMatchCoor m bax coor in
    let v1 = boxCoorPre box in 
    let w = coorMorph box in
    let v2 = boxCoorPost box in 
    (bax , loc' , Tran 30 v1 w box (Tran 30 w v2 bux mode))

clickLine :: (Float , Float) -> World -> Maybe World
clickLine mp (World m loc (q , size , ori) info _ law ext) =
    let (_ , linfo) = pictureMorphI size ori m loc in
    clickLineCheck mp linfo >>= \((x , y) , i , j) ->
    let w = addId i j x y (World m loc (q , size , ori) info mp law ext) in
    Just w
clickLine _ w = return w

clickNode :: (Float , Float) -> Float -> Morph -> [(Float , Float , Bool)] -> Maybe [(Float , Float , Bool)]
clickNode (mx , my) bs (Op m _ o) ((x , y , _) : l) = let os = sizeOper o in
    if abs (mx-x) <= bs*os && abs (my-y) <= bs*os then
        Just ((mx , my , True) : deselectNode l)
    else
        fmap ((x , y , False) :) (clickNode (mx , my) bs m l)
clickNode _ _ _ _ = Nothing

autostep :: World -> IO World
autostep (World m loc (q , size , ori) (goal , x , hist , moder , name) p page ext) =
    case anyredFull size m loc (fmap fst (equivStruc (pagePar page))) of
        Just (n , _)     ->
            let (v , w) = transCoor m n in
            return (World m loc (Tran 30 v w n Play , size , ori) (goal , x , hist , moder , name) p page ext)
        Nothing             ->  return (World m loc (q , size , ori) (goal , x , hist , moder , name) p page ext)
autostep w = return w

autostep2 :: World -> IO World 
autostep2 w =   let m = worldMorph w in 
                let (_ , size , ori) = wmode w in 
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
                        let (k , loc' , mode) = transitionAnim m box loc Play in
                        return (addHistory (RS x n name w') box n (w {morphism = k , coordinates = loc' , wmode = (mode , size , ori)}))
                        --return (w {morphism = n})

moveNode :: Point -> [(Float , Float , Bool)] -> [(Float , Float , Bool)]
moveNode _ [] = []
moveNode p ((x , y , False) : l)    =   (x , y , False) : moveNode p l
moveNode (mx , my) ((_ , _ , True) : l)     =   (mx , my , True) : moveNode (mx , my) l

newInfo :: Maybe (Rew , Morph , [Rew]) -> Rew -> Morph -> Bool 
newInfo Nothing _ _ = True 
newInfo (Just (rew , mor , _)) rew' mor' = rew /= rew' || mor /= mor'

infoNode :: Par Morph -> (Float , Float) -> Float -> Morph -> [(Float , Float , Bool)] -> MR 
    -> Maybe (Rew , Morph , [Rew]) -> Maybe (Rew , Morph , [Rew])
infoNode _ _ _ (Start _) _ _ _ = Nothing
infoNode _ _ _ _ [] _ _ = Nothing
infoNode par (mx , my) bs (Op m _ o) ((x , y , _) : l) moder old = let os = sizeOper o in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        case o of
            Comp n nh   ->  if newInfo old n nh 
                            then Just (n , nh , extractRew moder n nh par) 
                            else old 
            op          ->  let n = operMorph op in
                            if newInfo old (RI n) n
                            then Just (RI n , n , extractRew moder (RI n) n par)
                            else old
    else
        infoNode par (mx , my) bs m l moder old


-- rewriteNode (rewrite moder (pagePar pages)) (rePoint (getOri w) (mx , my)) (boxsize size m) m loc


-- the right click action
unfoldNode :: World -> (Float , Float) -> Float -> Morph -> [(Float , Float , Bool)] -> IO World
unfoldNode w p bs m lis = 
    case unfoldNode' p bs m lis 0 of
        Just (rw , wm , wl , q) ->  
            let w' = w {morphism = wm , coordinates = wl} in
            let h1 = unfoldBaseExcept m q in
            let h2 = unfoldBase wm in
            do {putStrLn (morphSaveX 0 m) ; return (addHistory rw h1 h2 w')}
        _                   ->  return w


unfoldNode' :: (Float , Float) -> Float -> Morph ->  [(Float , Float , Bool)] -> Int -> Maybe (Rew , Morph , [(Float , Float , Bool)] , Int)
unfoldNode' _ _ (Start _) _ _ = Nothing --World (Start i) r (q , size) (g , [] , hist , name) mp law
unfoldNode' _ _ _ [] _ = Nothing
unfoldNode' (mx , my) bs (Op m i (Comp n nh)) ((x , y , k) : r) q =
    let os = sizeOper (Comp n nh) in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        let n' = weakenMorph i 0 (rewMorph n) in
        Just (n , compMorph n' m , fmap (\(s , t , _) -> (s + x - bs*os , t + y - bs*os , False)) (initCoor' (2*bs*os) n') ++ r , q)
    else
        unfoldNode' (mx , my) bs m r (q+1) >>= \(wr , wm , wl , q') ->
            Just (wr , Op wm i (Comp n nh) , (x , y , k) : wl , q')
unfoldNode' (mx , my) bs (Op m i (Func "I" n)) ((x , y , k) : r) q =
    let os = sizeOper (Func "I" n) in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        let n' = weakenMorph i 0 n in
        Just (RI n , compMorph n' m , fmap (\(s , t , _) -> (s + x - bs , t + y - bs , False)) (initCoor' (2*bs) n') ++ r , q)
    else
        unfoldNode' (mx , my) bs m r (q+1) >>= \(wr , wm , wl , q') ->
            Just (wr , Op wm i (Func "I" n) , (x , y , k) : wl , q')
unfoldNode' (mx , my) bs (Op m i op) ((x , y , k) : r) q =
    unfoldNode' (mx , my) bs m r (q+1) >>= \(wr , wm , wl , q') ->
    Just (wr , Op wm i op , (x , y , k) : wl , q')


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
addHistory (RS x _ _ w) h1 m' (World m loc q (g , rew , ((n , hist) , hi) , moder , name) mp law ext) =
    case lookHist m' (proofSeq (n , hist)) of
        Just i                              ->  World m loc q (g , rew , ((n , hist) , i) , moder , name) mp law ext
        Nothing                             ->  World m loc q (g , rew , ((n , popList hi hist ++ [(m' , x , "?" , Axiom , h1)]) , 0) , moder , name) mp law ext
addHistory _ _ _ (World m loc q (g , rew , hist , moder , name) mp law ext)  =   World m loc q (g , rew , hist , moder , name) mp law ext
addHistory _ _ _ w = w

gotoHistory :: Morph -> World -> World
gotoHistory m' (World m loc q (g , rew , ((n , hist) , hi) , moder , name) mp law ext) =
    case lookHist m' (proofSeq (n , hist)) of
        Just i                              ->  World m loc q (g , rew , ((n , hist) , i) , moder , name) mp law ext
        Nothing                             ->  World m loc q (g , rew , ((n , hist) , hi) , moder , name) mp law ext
gotoHistory _ w = w


rightClick :: World -> (Float , Float) -> IO World
rightClick w (mx , my) | isPlay w =    
    let m = morphism w in
    let size = worldSize w in
    unfoldNode w (rePoint size (getOri w) (mx , my)) (boxsize (worldSize w) m) m (coordinates w) >>= \u ->
    return u
    --do {putStrLn (printMorphI (worldMorph u)) ; return u}
rightClick w (mx , my) | isEdit w = 
    let m = morphism w in
    let loc = coordinates w in
    let size = worldSize w in 
    let bs = boxsize size m in 
    let (n , roc) = deleteOp size (mx , my) bs m loc in 
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
    |   otherwise               =   let (relat , viv , theor , d1 , d2 , comment , file) = document w in
                                    let m = morphism w in
                                    let n = lastbox m m in
                                        prevState (w {document = (relat , viv , theor , d1 , toss (Displ (MEqual , n , n , "Focus" , Show) Nothing "Zoomed into a part of the diagram.") d2 , comment , file)})



newname :: [Sig] -> Maybe Char
newname op = newelem "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789" (fmap (\ (Sig c _ _ _) -> c) op)

stampAction :: Float -> World -> IO World
stampAction bs w = --(World m loc (q , size , ori) (goal , a , hist , moder , name) mp page ext)
    let m = morphism w in 
    let loc = coordinates w in
    let (_ , _ , ori) = wmode w in 
    let mp = mouse w in
    let page = document w in 
    let size = worldSize w in
    case newname (pageSig page) of
        Just c      ->  case defineOption c (rePoint size ori mp) bs m loc page 0 of 
            Just  (m' , r' , page' , box , q') ->
                        return (addHistory (RS MEqual m' "" Axiom) (unfoldBaseExcept box q') (unfoldBase m') (w {morphism = m' , coordinates = r' , document = page'}))
            Nothing     ->  return w 
        Nothing     ->  return w


defineOption :: Char -> Point -> Float -> Morph -> [(Float , Float , Bool)] -> Page -> Int 
    -> Maybe (Morph , [(Float , Float , Bool)] , Page , Morph , Int)
defineOption _ _ _ (Start _) _ _ _ = Nothing
defineOption _ _ _ _ [] _ _ = Nothing
defineOption c (mx , my) bs (Op m i (Comp rew n)) ((x , y , k) : r) (rel , v , (sig , hem , relat , par) , d1 , d2 , comment , file) q =
    let os = sizeOper (Comp rew n) in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        let (ni , no) = typeMorph n in
        let sig' = addSet (Sig c (Nothing ,"") ni no) sig in
        let hem' = addCompOp (Sig c (Nothing ,"") ni no) (morphOps n) hem in
        let opm = operMorph (Base (Sig c (Nothing ,"") ni no)) in
        let name = "Definition of " ++ [c] in
        let neweqs = (newOp hem' (Sig c (Nothing ,"") ni no) ++ [(MEqual , opm , n , name , Axiom)]) in
        let relat' =  filterAdd' neweqs relat in
        let par' = addRelatsPar neweqs par in
        let page' = (rel , v , (sig' , hem' , relat' , par') , d1 , d2 , comment , file) in
        Just (Op m i (Base (Sig c (Nothing ,"") ni no)) , (x , y , k) : r , page' , 
                Op m i (Comp (RS MEqual opm name Axiom) n) , q)
    else
        defineOption c (mx , my) bs m r (rel , v , (sig , hem , relat , par) , d1 , d2 , comment , file) (q+1) >>= \(m' , r' , page' , box , q') ->
        Just (Op m' i (Comp rew n) , (x , y , k) : r' , page' , Op box i (Comp rew n) , q')
defineOption c mp bs (Op m i op) ((x , y , k) : r) law q =
    defineOption c mp bs m r law (q+1) >>= \(m' , r' , law' , box , q') ->
    Just (Op m' i op , (x , y , k) : r' , law' , Op box i op , q')


addCurrentRel :: World -> World
addCurrentRel (Load x y z) = Load x y z
addCurrentRel w =
    let (_ , _ , (rews , _) , _ , name) = winfo w in
    let newrelat = extractRel (name ++ "X") Lemma (morphism w) (proofSeq rews) MEqual in
    let (rel , v , (sigs , schem , relat , par) , d1 , d2 , comment , file) = document w in
    let relats = newrelat : newRelats schem [newrelat] in
    let theor' = (sigs , schem , filterAdd' relats relat , addRelatsPar relats par) in
        w {document = (rel , v , theor' , d1 , toss (Assum newrelat) d2 , comment , file)}


extractRel :: String -> Why -> Morph -> [Rew] -> MR -> Relat
extractRel name w m [] _ = (MEqual , m , m , name , w)
extractRel name w m [RI n] y = (y , m , n , name , w)
extractRel name w m [RS x n _ _] y = (joinMRunsafe x y , m , n , name , w)
extractRel name w m ((RI _) : l) y = extractRel name w m l y
extractRel name w m ((RS x _ _ _) : l) y = extractRel name w m l (joinMRunsafe x y)


deleteOp :: Float -> Point -> Float -> Morph -> [(Float , Float , Bool)] -> (Morph , [(Float , Float , Bool)])
deleteOp size (mx , my) bs (Op m i op) ((x , y , b) : loc)
    |   abs (mx - x) <= bs && abs (my - y) <= bs    =   (m , loc)
    |   otherwise                                   =   
            let (n , roc) = deleteOp size (mx , my) bs m loc in 
            case checkMorph (Op n i op) of 
                Just _      ->  (Op n i op , (x , y , b) : roc)
                _           ->  (Op m i op , (x , y , b) : loc)
deleteOp _ _ _ m loc = (m , loc)