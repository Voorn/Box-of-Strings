module Event where

-- standard library
import Data.Maybe
import Data.Bifunctor

-- extended libraries
import Graphics.Gloss
import Graphics.Gloss.Interface.IO.Interact
import Graphics.Gloss.Interface.IO.Game
import Graphics.Gloss.Interface.Environment
import System.Exit
import System.Directory

-- project libraries
import Morph
import Rewrite
import Display
import Parse
import Theory
import Par
import World
-- semantic addition
import SemanticFree


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
    selectMenu size (mouseMenu size (tM size p)) l (Load size (tM size p) l)
event (EventMotion p) (Load size _ l) = return (Load size (tM size p) l)
event _ (Load size p l) = return (Load size p l)

-- when transitioning, don't do anything
event (EventMotion p) (World m loc (Tran x y z w t , size , ori) (goal , a , hist , moder , name) _ law) =
    return (World m loc (Tran x y z w t , size , ori) (goal , a , hist , moder , name) (tM size p) law)
event _ (World m loc (Tran x y z w t , size , ori) (goal , a , hist , moder , name) p law) =
    return (World m loc (Tran x y z w t , size , ori) (goal , a , hist , moder , name) p law)

-- when displaying
event (EventKey (MouseButton LeftButton) Down _ p) (World m loc (Disp _ , size , ori) (goal , a , hist , moder , name) _ law) =
    return (World m loc (Play , size , ori) (goal , a , hist , moder , name) p law)
event (EventKey (MouseButton WheelUp) Down _ _) (World m loc (Disp v , size , ori) (goal , a , hist , moder , name) p law) =
    return (World m loc (Disp (v+1) , size , ori) (goal , a , hist , moder , name) p law)
event (EventKey (MouseButton WheelDown) Down _ _) (World m loc (Disp v , size , ori) (goal , a , hist , moder , name) p law) =
    return (World m loc (Disp (v-1) , size , ori) (goal , a , hist , moder , name) p law)
event (EventMotion p) (World m loc (Disp v , size , ori) (goal , a , hist , moder , name) _ law) =
    return (World m loc (Disp v , size , ori) (goal , a , hist , moder , name) (tM size p) law)
event _ (World m loc (Disp v , size , ori) (goal , a , hist , moder , name) p law) =
    return (World m loc (Disp v , size , ori) (goal , a , hist , moder , name) p law)

-- semantics
event (EventKey (Char 'p') Down _ _) (World m loc (q , size , ori) info p law)
    = do
        putStrLn "\n=== SEMANTIC PIPELINE ==="
        putStrLn "\n--- Morphism to Free Semantic ---"
        let sem = morphToSemantic m
        mapM_ putStrLn (prettySemantic sem)
        return (World m loc (q , size , ori) info p law)

-- animation
event _ (World m loc (Anim i , size , ori) (goal , a , hist , moder , name) p law) =
    return (World m loc (Anim i , size , ori) (goal , a , hist , moder , name) p law)

event (EventKey (MouseButton LeftButton) Down _ p) w
    =   clickEvent (tM (worldSize w) p) w >>= \v -> event (EventMotion p) v
event (EventKey (MouseButton LeftButton) Up _ _) (World m loc q info mp law)
    =   return (World m (deselectNode loc) q info mp law)
event (EventKey (MouseButton RightButton) Down _ p) (World m loc (q , size , ori) (goal , _ , hist , moder , name) _ law)
    =   rightClick size ori q (tM size p) (boxsize size m) m loc goal hist moder name law
--event (EventKey (MouseButton MiddleButton) Down _ p) (m , loc , (goal , _ , hist , name) , _ , law)
--    =   middleClick (tM p) (boxsize size m) m loc goal hist name law
event (EventKey (SpecialKey KeyTab) Down _ _) (World m loc (q , size , ori) (goal , wow , hist , moder , name) p (sig , hem , rew , file))
    =   do {
        writeFile "tex/test.tex" (allTikz name (relatWrap moder (firstRew (reverse (fst hist))) (firstRew (reverse goal))) (reverse (fst hist) ++ tailList goal))
        ; return (World m loc (q , size , ori) (goal , wow , hist , moder , name) p (sig , hem , rew , file))}
event (EventKey (MouseButton WheelUp) Down _ p) (World m loc (q , size , ori) (goal , _ , hist , moder , name) _ (sig , hem , rew , file))
    =   let n = rewriteNode (rewrite moder rew) (rePoint ori (tM size p)) (boxsize size m) m loc in
        return (World n loc (q , size , ori) (goal , infoNode rew (tM size p) (boxsize size n) n loc moder , hist , moder , name) (tM size p) (sig , hem , rew , file))
event (EventKey (MouseButton WheelDown) Down _ p) (World m loc (q , size , ori) (goal , _ , hist , moder , name) _ (sig , hem ,rew , file))
    =   let n = rewriteNode (dewrite moder rew) (rePoint ori (tM size p)) (boxsize size m) m loc in
        return (World n loc (q , size , ori) (goal , infoNode rew (tM size p) (boxsize size n) n loc moder , hist , moder , name) (tM size p) (sig , hem , rew , file))
event (EventMotion p) (World m loc (q , size , ori) (goal , _ , hist , moder , name) _ (sig , hem , rew , file))
    =   return (World m (moveNode (rePoint ori (tM size p)) loc) (q , size , ori)
                (goal , infoNode rew (rePoint ori (tM size p)) (boxsize size m) m loc moder , hist , moder , name) (tM size p) (sig , hem ,rew , file))
event (EventKey (SpecialKey KeySpace) Down _ _) w = autostep w
-- type mods 
-- event (EventKey (SpecialKey KeyTab) Down _ _) w = do {putStrLn (printMorphI (rState w)) ; return w}
event (EventKey (MouseButton MiddleButton) Down _ _) w = stampAction (boxsize (worldSize w) (worldMorph w)) w
-- modifications
event (EventKey (SpecialKey KeyDelete) Down _ _) (World m (_ : loc) (Edit , size , ori) (goal , _ , hist , moder , name) mp law) =
    return (World (removeLast m) loc (Edit , size , ori) (goal , [] , hist , moder , name) mp law)
event (EventKey (SpecialKey KeyRight) Down _ _) (World m loc (Edit , size , ori) (goal , _ , hist , moder , name) mp law) =
    return (World (extraWire m) loc (Edit , size , ori) (goal , [] , hist , moder , name) mp law)
event (EventKey (SpecialKey KeyLeft) Down _ _) (World m loc (Edit , size , ori) (goal , _ , hist , moder , name) mp law) =
    return (World (removeWire m) loc (Edit , size , ori) (goal , [] , hist , moder , name) mp law)
event (EventKey (SpecialKey KeyUp) Down _ _) (World m loc (Edit , size , ori) (goal , _ , hist , moder , name) mp law) =
    return (World (upLast m) loc (Edit , size , ori) (goal , [] , hist , moder , name) mp law)
event (EventKey (SpecialKey KeyDown) Down _ _) (World m loc (Edit , size , ori) (goal , _ , hist , moder , name) mp law) =
    return (World (downLast m) loc (Edit , size , ori) (goal , [] , hist , moder , name) mp law)
event (EventKey (Char c) Down (Modifiers _ _ ct) _) (World m loc (Edit , size , ori) (goal , _ , hist , moder , name) mp (sig , hem ,rew , file))
    = case numParse' c of
        Just k      ->  if ct == Down   then return (World (outOper k m) loc (Edit , size , ori) (goal , [] , hist , moder , name) mp (sig , hem ,rew , file))
                                            else return (World (inpOper k m) loc (Edit , size , ori) (goal , [] , hist , moder , name) mp (sig , hem ,rew , file))
        Nothing     ->  case findMorph sig c of
            Just (Sig d s i j)  ->  return (World (addOper (Sig d s i j) m) ((size/2 , size/2 , False) : loc) (Edit , size , ori) (goal , [] , hist , moder , name) mp (sig , hem ,rew , file))
            Nothing             ->  return (World (Op m 0 (Base (Sig c "" 0 1))) ((0 , 0 , False) : loc) (Edit , size , ori) (goal , [] , hist , moder , name) mp (sig , hem , rew , file))
-- help
event (EventKey (SpecialKey KeyDown) Down x p) w = event (EventKey (MouseButton WheelDown) Down x p) w
event (EventKey (SpecialKey KeyUp) Down x p) w = event (EventKey (MouseButton WheelUp) Down x p) w
--event (EventKey (SpecialKey KeySpace) Down _ _) w = nextState w
    --let file' = incfile file in 
    --readinfo file' >>= \info -> return (setWorld2 file' info)
--event _ _ (EventKey (SpecialKey KeySpace) Down _ _) _ = exitWith ExitSuccess
event _ w = return w

nextState :: World -> IO World
nextState (Load size p l) = return (Load size p l)
nextState (World _ _ (_ , size , ori) (_ , _ , _ , _ , _) _ (op , hem ,eqs , file)) = return (phaseWorld size ori op hem eqs file)

--        _                               ->
--            getDirectoryContents "input" >>= \s ->
--            return (Load size p (tryAll stripTxt s))

-- ======================
-- The Core step function
-- ======================

step :: Float -> World -> IO World
step _ (Load size p l) = return (Load size p l)
step _ (World m loc (Anim i , size , ori) (goal , rew , (hist , hi) , moder , name) mp law)
    |   hi <= 0                 =   return (World m loc (Play , size , ori) (goal , rew , (hist , hi) , moder , name) mp law)
    |   i <= 0                  =   let n = looku (hi-1) (RI m) hist in
                                    let (v , w) = transCoor m (rewMorph n) in
                                    return (World m loc (Tran 30 v w (rewMorph n) (Anim 30), size , ori) (goal , rew , (hist , hi - 1) , moder , name) mp law)
    |   otherwise               =   let app = initCoor size m in
                                    return (World m (approach (1/ fromIntegral i) loc app) (Anim (i-1) , size , ori) (goal , rew , (hist , hi) , moder , name) mp law)
step _ (World m loc (Tran i app new n t , size , ori) (goal , rew , hist , moder , name) mp law)
    |   i <= 0      =   return (addHistory (RS MEqual n) (World n (fmap (\(x , y) -> (size*x , size*y , False)) new) (t , size , ori) (goal , rew , hist , moder , name) mp law))
    |   otherwise   =   return (World m (approach (1/ fromIntegral i) loc
                                (fmap (bimap (size *) (size *)) app)) (Tran (i-1) app new n t , size , ori) (goal , rew , hist , moder , name) mp law)
step _ (World m loc (Disp v , size , ori) (goal , rew , hist , moder , name) mp law) = return (World m loc (Disp v , size , ori) (goal , rew , hist , moder , name) mp law)
step _ (World m loc (q , size , ori) (goal , rew , hist , moder , name) mp law) =
    case worldAll (World m loc (q , size , ori) (goal , rew , hist , moder , name) mp law) of
        Just n      ->  return n
        Nothing     ->
            let app = initCoor size m   in
            return (World m (approach (1/30) loc app) (q , size , ori) (goal , rew , hist , moder , name) mp law)

-- Start application from loading a file
playLoad :: Bool -> Maybe Int -> IO ()
playLoad full Nothing =
    getScreenSize >>= \t -> let size = if full then sizzle t else sizzle t * 0.9 in
    getDirectoryContents "input" >>= \s ->
    playIO (setDisplay full size) setColor setSim (Load size (0,0) (mapMaybe stripTxt s)) displayWorld event step
playLoad full (Just i) =
    let size = fromIntegral i in
    getDirectoryContents "input" >>= \s ->
    playIO (setDisplay full size) setColor setSim (Load size (0,0) (mapMaybe stripTxt s)) displayWorld event step


-- =================
-- Actions
-- =================

-- Unsafe
addId :: Int -> Int -> Float -> Float -> World -> World
addId _ w x y (World (Start i) loc q info mp law) = World (Op (Start i) w (Comp (RI (Start 1)) (Start 1))) ((x , y , True) : loc) q info mp law
addId _ _ _ _ (World (Op m i o) [] q info mp law) = World (Op m i o) [] q info mp law
addId d w x y (World (Op m i o) ((a , b , _) : loc) q info mp law)
    |   d <= 0      =   World (Op (Op m i o) w (Comp (RI (Start 1)) (Start 1))) ((x , y , False) : (a , b , False) : loc) q info mp law
    |   otherwise   =   let ww = addId (d-1) w x y (World m loc q info mp law) in
                            World (Op (worldMorph ww) i o) ((a , b , False) : worldLoc ww) q info mp law
addId _ _ _ _ w = w

deselectNode :: [(Float , Float , Bool)] -> [(Float , Float , Bool)]
deselectNode = fmap (\(a , b , _) -> (a , b , False))

clickLineCheck :: (Float , Float) -> [(Point , Int, Int)] -> Maybe (Point , Int , Int)
clickLineCheck _ [] = Nothing
clickLineCheck (mx , my) (((x , y) , i , j) : r)
    |   abs (mx-x) <= 10 && abs (my-y) <= 10    =   Just ((x , y) , i , j)
    |   otherwise                                       =   clickLineCheck (mx , my) r

clickEvent :: (Float , Float) -> World -> IO World
clickEvent (mx , my) (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) _ law)
-- right bar menu
    -- Open equation list
    |   mx >= size && my <= size*0.125
                    =   return (World m loc (Disp 0 , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law)
    -- Load file 
    |   mx >= size && my <= size*0.25
                    =   getDirectoryContents "input" >>= \s ->
                        return (Load size (mx , my) (mapMaybe stripTxt s))
    -- Next equation
    |   mx >= size && my >= size*0.875
                    =   nextState (World m loc (Disp 0 , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law)
    -- Apply autoreduction step
    |   mx >= size && my >= size*0.75
                    =   autostep (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law)
    -- Flip
    |   mx >= size && my >= size*0.625
                    =   return (World m loc (q , size , flipOrient ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law)
-- left bar history
    |   mx <= 0     =   let hn = length hist in
                        let i = scrollSelect size my (hn + length goal) in
                        if i <= -1 then
                            return (World m loc (Anim 10 , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law)
                        else
                        if i < hn then
                            let n = looku i m (fmap  rewMorph (reverse hist)) in
                            let (v , w) = transCoor m n in
                            return (World m loc (Tran 30 v w n Play , size , ori) (goal , rew , (hist , length hist - 1 - i) , moder , name) (mx , my) law)
                        else
                            let n = looku (i - hn) m (fmap rewMorph goal) in
                            let (v , w) = transCoor m n in
                            return (World m loc (Tran 30 v w n Play , size , ori) (reverseSih hist , rew , (reverseHis goal , i - hn) , reverseMR moder , name) (mx , my) law)
-- workbench
    |   otherwise   =   case clickNode (rePoint ori (mx , my)) (boxsize size m) m loc of
            Just roc    ->  return (World m roc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law)
            Nothing     ->  case clickLine (rePoint ori (mx , my)) (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law) of
                Just w  ->  return w
                Nothing ->  return (World m loc (q , size , ori) (goal , rew , (hist , hi) , moder , name) (mx , my) law)
clickEvent _ w = return w

clickLine :: (Float , Float) -> World -> Maybe World
clickLine mp (World m loc (q , size , ori) info _ law) =
    let (_ , linfo) = pictureMorphI size ori m loc in
    clickLineCheck mp linfo >>= \((x , y) , i , j) ->
    let w = addId i j x y (World m loc (q , size , ori) info mp law) in
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
autostep (World m loc (q , size , ori) (goal , x , hist , moder , name) p (sig , hem ,rew , file)) =
    case anyredFull size m loc (fmap fst rew) of
        Just (n , _)     ->
            let (v , w) = transCoor m n in
            return (World m loc (Tran 30 v w n Play , size , ori) (goal , x , hist , moder , name) p (sig , hem , rew , file))
        Nothing             ->  return (World m loc (q , size , ori) (goal , x , hist , moder , name) p (sig , hem , rew , file))
autostep w = return w

moveNode :: Point -> [(Float , Float , Bool)] -> [(Float , Float , Bool)]
moveNode _ [] = []
moveNode p ((x , y , False) : l)    =   (x , y , False) : moveNode p l
moveNode (mx , my) ((_ , _ , True) : l)     =   (mx , my , True) : moveNode (mx , my) l

infoNode :: Par Morph -> (Float , Float) -> Float -> Morph -> [(Float , Float , Bool)] -> MR -> [Rew]
infoNode _ _ _ (Start _) _ _ = []
infoNode _ _ _ _ [] _ = []
infoNode par (mx , my) bs (Op m _ o) ((x , y , _) : l) moder = let os = sizeOper o in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        case o of
            Comp n nh                           ->  extractRew moder n nh par --rewMorph n : reverse (equivPop (rewMorph n) [] (fmap fst rew))
            Base (Sig fc fs a b)                ->  extractRew moder (RI (Op (Start a) 0 (Base (Sig fc fs a b)))) (Op (Start a) 0 (Base (Sig fc fs a b))) par --Op (Start a) 0 (Base (Sig fc fs a b)) : reverse (equivPop (Op (Start a) 0 (Base (Sig fc fs a b))) [] (fmap fst rew))
    else
        infoNode par (mx , my) bs m l moder


-- the right click action
unfoldNode :: Float -> Orient -> Mode -> (Float , Float) -> Float -> Morph -> [(Float , Float , Bool)] -> [Rew] -> ([Rew] , Int) -> MR -> String
    -> Theory -> World
unfoldNode size ori q p bs m lis g hist moder name law = case unfoldNode' size ori q p bs m lis g hist moder name law of
    Just (rw , ww)      ->  addHistory rw ww
    _                   ->  World m lis (q , size , ori) (g , [] , hist , moder , name) p law


unfoldNode' :: Float -> Orient -> Mode -> (Float , Float) -> Float -> Morph -> [(Float , Float , Bool)] -> [Rew] -> ([Rew] , Int) -> MR -> String
    -> Theory -> Maybe (Rew , World)
unfoldNode' _ _ _ _ _ (Start _) _ _ _ _ _ _ = Nothing --World (Start i) r (q , size) (g , [] , hist , name) mp law
unfoldNode' _ _ _ _ _ _ [] _ _ _ _ _ = Nothing
unfoldNode' size ori q (mx , my) bs (Op m i (Base (Sig fc fs fi fo))) ((x , y , k) : r) g hist moder name law =
    unfoldNode' size ori q (mx , my) bs m r g hist moder name law >>= \(wr , ww) ->
    Just (wr , World (Op (worldMorph ww) i (Base (Sig fc fs fi fo))) ((x , y , k) : worldLoc ww) (q , size , ori) (g , [] , hist , moder , name) (mx , my) law)
unfoldNode' size ori q (mx , my) bs (Op m i (Comp n nh)) ((x , y , k) : r) g hist moder name law =
    let os = sizeOper (Comp n nh) in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        let n' = weakenMorph i 0 (rewMorph n) in
        Just (n , World (compMorph n' m) (fmap (\(s , t , _) -> (s + x - bs , t + y - bs , False)) (initCoor' (2*bs) n') ++ r) (q , size , ori) (g , [] , hist , moder , name) (mx , my) law)
    else
        unfoldNode' size ori q (mx , my) bs m r g hist moder name law >>= \(wr , ww) ->
            Just (wr , World (Op (worldMorph ww) i (Comp n nh)) ((x , y , k) : worldLoc ww) (q , size , ori) (g , [] , hist , moder , name) (mx , my) law)

-- Unfold all composites into their former base
unfoldBase :: Morph -> Morph
unfoldBase (Start i)            =   Start i
unfoldBase (Op m i (Base s))    =   Op (unfoldBase m) i (Base s)
unfoldBase (Op m i (Comp _ n))  =   let n' = weakenMorph i 0 n in
                                    compMorph n' (unfoldBase m)



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

addHistory :: Rew -> World -> World
addHistory (RS x _) (World m loc q (g , rew , (n : hist , hi) , moder , name) mp law) =
    let m' = unfoldBase m in
    case lookHist m' (n : hist) of
        Just i                              ->  World m loc q (g , rew , (n : hist , i) , moder , name) mp law
        Nothing                             ->  World m loc q (g , rew , (RS x m' : dookHist hi (n : hist) , 0) , moder , name) mp law
addHistory _ (World m loc q (g , rew , hist , moder , name) mp law)  =   World m loc q (g , rew , hist , moder , name) mp law
addHistory _ w = w

rightClick :: Float -> Orient -> Mode -> (Float , Float) -> Float -> Morph -> [(Float , Float , Bool)] -> [Rew] -> ([Rew] , Int) -> MR -> String
    -> Theory -> IO World
rightClick size ori q (mx , my) x m loc g (hist , hi) moder name law
                          = let u = unfoldNode size ori q (rePoint ori (mx , my)) x m loc g (hist , hi) moder name law in
                            do {putStrLn (printMorphI (worldMorph u)) ; return u}


newelem :: Eq a => [a] -> [a] -> Maybe a
newelem [] _ = Nothing
newelem (a : z) s
    |   inList a s  =   newelem z s
    |   otherwise   =   Just a


newname :: [Sig] -> Maybe Char
newname op = newelem "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789" (fmap (\ (Sig c _ _ _) -> c) op)

stampAction :: Float -> World -> IO World
stampAction bs (World m loc (q , size , ori) (goal , a , hist , moder , name) mp (sig , hem , rew , file)) =
    case newname sig of
        Just c      ->  return (addHistory (RS MEqual m) (defineOption c size ori q (rePoint ori mp) bs m loc goal hist moder name (sig , hem , rew , file)))
        Nothing     ->  return (World m loc (q , size , ori) (goal , a , hist , moder , name) mp (sig , hem , rew , file))
stampAction _ w = return w


defineOption :: Char -> Float -> Orient -> Mode -> (Float , Float) -> Float -> Morph -> [(Float , Float , Bool)] -> [Rew] -> ([Rew] , Int) -> MR -> String
    -> Theory -> World
defineOption _ size ori q mp _ (Start i) r g hist moder name law =
    World (Start i) r (q , size , ori) (g , [] , hist , moder , name) mp law
defineOption _ size ori q mp _ m [] g hist moder name law =
    World m [] (q , size , ori) (g , [] , hist , moder , name) mp law
defineOption c size ori q (mx , my) bs (Op m i (Base (Sig fc fs  fi fo))) ((x , y , k) : r) g hist moder name law =
    let ww = defineOption c size ori q (mx , my) bs m r g hist moder name law in
    World (Op (worldMorph ww) i (Base (Sig fc fs fi fo))) ((x , y , k) : worldLoc ww) (q , size , ori) (g , [] , hist , moder , name) (mx , my) (worldLaw ww)
defineOption c size ori q (mx , my) bs (Op m i (Comp n nh)) ((x , y , k) : r) g hist moder name (sig , hem , eqs , nex) =
    let os = sizeOper (Comp n nh) in
    if abs (mx-x) <= os*bs && abs (my-y) <= os*bs then
        let (ni , no) = typeMorph (rewMorph n) in
        let sig' = addSet (Sig c "" ni no) sig in
        let hem' = addCompOp (Sig c "" ni no) (morphOps (rewMorph n)) hem in
        let eqs' = addrelClass (newOp hem' (Sig c "" ni no) ++ [(MEqual , operMorph (Base (Sig c "" ni no)) , rewMorph n)]) eqs in
        World (Op m i (Base (Sig c "" ni no))) ((x , y , k) : r) (q , size , ori) (g , [] , hist , moder , name) (mx , my) (sig' , hem' , eqs' , nex)
    else
        let ww = defineOption c size ori q (mx , my) bs m r g hist moder name (sig , hem , eqs , nex) in
        World (Op (worldMorph ww) i (Comp n nh)) ((x , y , k) : worldLoc ww) (q , size , ori) (g , [] , hist , moder , name) (mx , my) (worldLaw ww)

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
checkSwapMulti (x : l) w = case checkSwapGen x w of
    Just v      ->  Just v
    Nothing     ->  checkSwapMulti l w

checkSwapGen :: (Int , Bool , Bool , Bool) -> World -> Maybe World
checkSwapGen _ (World (Start _) _ _ _ _ _) = Nothing
checkSwapGen _ (World _ [] _ _ _ _) = Nothing
checkSwapGen (d , v , w , a) (World (Op m i o) (x : l) q info mp law)
    |   d <= 0      =   checkSwap v w a (World (Op m i o) (x : l) q info mp law)
    |   otherwise   =   checkSwapGen (d-1 , v , w , a) (World m l q info mp law) >>=
            \ww -> Just (World (Op (worldMorph ww) i o) (x : worldLoc ww) q (worldInfo ww) mp law)
checkSwapGen _ w = return w

checkSwap :: Bool -> Bool -> Bool -> World -> Maybe World
checkSwap v w a (World (Op (Op m j q) i o) ((x , y , _) : (x' , y' , _) : r) p info mp law) =
    let (oi , oo) = typeOper o in
    let (qi , qo) = typeOper q in
    if oi == 0 && qo == 0 && i == j then
        if not a then
            Just (World (Op (Op m (i-qo+qi) o) j q) ((x' , y' , v) : (x , y , w) : r) p info mp law)
        else
            Just (World (Op (Op m i o) (j-oi+oo) q ) ((x' , y' , v) : (x , y , w) : r) p info mp law)
    else
        if (j + qo) <= i then
            Just (World (Op (Op m (i-qo+qi) o) j q) ((x' , y' , v) : (x , y , w) : r) p info mp law)
        else
            if (i + oi) <= j then
                Just (World (Op (Op m i o) (j-oi+oo) q) ((x' , y' , v) : (x , y , w) : r) p info mp law)
            else
                Nothing
checkSwap _ _ _ _ = Nothing

-- Checking whether a node dragged out of place creates a swap. Returns world with swap executed.
worldSwap :: World -> Maybe World
worldSwap (World m loc q info mp law) = worldSwapGen 0 (World m loc q info mp law) >>= \k -> checkSwapMulti k (World m loc q info mp law)
worldSwap w = Just w

-- Checks whether a node as been dragged out of place, giving options for checking what to swap.
-- Returns: (node index of swap, first node held, second node held, over or under)
worldSwapGen :: Int -> World -> Maybe [(Int , Bool , Bool , Bool)]
worldSwapGen q (World (Op m _ _) ((a , b , k) : (c , d , v) : l) p info mp law)
    |   a < c && (k || v)   =   if k    then    Just [(q , False , True , b < d) , (q+1 , False , False , True)]
                                        else    Just [(q , True , False , b < d) , (q-1 , False , False , True)]
    |   otherwise           =   worldSwapGen (q+1) (World m ((c , d , v) : l) p info mp law)
worldSwapGen _ _ = Nothing



worldMerge :: World -> Float -> Maybe World
worldMerge (World (Op (Op m j p) i o) ((a , b , k) : (c , d , v) : l) t info (mx , my) law) bs = let os = (sizeOper o + sizeOper p - 1) in
    if abs (a-c) <= bs*os && abs (b-d) <= bs*os && (k || v) then
        checkMerge (Op (Op m j p) i o) >>= \n -> Just (World n ((mx , my, True) : l) t info (mx , my) law)
    else
        worldMerge (World (Op m j p) ((c , d , v) : l) t info (mx , my) law) bs >>= \ww
            ->  Just (World (Op (worldMorph ww) i o) ((a , b , k) : worldLoc ww) t (worldInfo ww) (mx , my) law)
worldMerge _ _ = Nothing

worldAll :: World -> Maybe World
worldAll (World m loc (q , size , ori) info mp law) =
    case worldSwap (World m loc (q , size , ori) info mp law) of
        Just w      ->  Just w
        Nothing     ->  worldMerge (World m loc (q , size , ori) info mp law) (boxsize size m)
worldAll w = Just w

readinfo :: String -> IO [Phase]
readinfo file = readFile ("input/" ++ file ++ ".txt") >>= \s ->
    let z = strip s in return (parseAll [] [] z)

stripTxt :: FilePath -> Maybe String
stripTxt [] = Nothing
stripTxt ".txt" = Just ""
stripTxt (c : l) = fmap (c :) (stripTxt l)



--readI :: Bool -> IO ()
--readI full =
--    getDirectoryContents "input" >>= \s -> do {print s ;
--    putStrLn "Type file name here:" ; getLine >>= \file ->
--    readinfo file >>= \((m , g , ms , eqs' , name) , l) -> playAll full m g ms name eqs' l}
