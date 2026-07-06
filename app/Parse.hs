{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Replace case with fromMaybe" #-}
module Parse where

-- standard libraries
import Data.Bifunctor

-- in project libraries
import Matcher
import Morph
--import Rewrite
import Theory
import Par2
import Proof

type Mem = (Morph , Int , Proof , Maybe Proof)

proofMem :: Proof -> Mem 
proofMem (m , l) = (m , length l , (m , l) , Just (proofGoal (m , l) , []))

-- attempt to clean up a bit
-- Display instructions: concrete step for what to add and what to display
data Disp = Opera Sig
        |   Schem Schema
        |   Assum Relat
        |   Displ Relat (Maybe Mem) String
    deriving Show

-- A theory contains a signature, as list of schema, and a data structure of relations
type Theor = ([Sig] , [Schema] , [Relat] , Par Morph)

-- flushing operations removes any mention of a certain operation
flushRelat :: Char -> [Relat] -> [Relat]
flushRelat _ [] = []
flushRelat c ((moder, m , n , name , w) : l) 
    |   opinMorph c m || opinMorph c n  =   flushRelat c l
    |   otherwise                       =   (moder, m , n , name , w) : flushRelat c l

flushTheor :: Char -> Theor -> Theor 
flushTheor c (sigs , schem , relat , par) = (flushSig c sigs , flushSchema c schem , flushRelat c relat , flushPar c par)

cleaneq :: Morph -> Morph -> Bool 
cleaneq m n = cleanMorph m == cleanMorph n

filterAdd :: Relat -> [Relat] -> [Relat]
filterAdd a [] = [a]
filterAdd (x , a , b , p , w) ((y , c , d , q , v) : l)
    |   orderMR y x && cleaneq a c && cleaneq b d                 =   (y , c , d , q , v) : l
    |   orderMR y (reverseMR x) && cleaneq b c && cleaneq a d     =   (y , c , d , q , v) : l
    |   otherwise                                       =   (y , c , d , q , v) : filterAdd (x , a , b , p , w) l

filterAdd' :: [Relat] -> [Relat] -> [Relat]
filterAdd' l r = foldl (flip filterAdd) r l

simpRelat :: Relat -> Relat 
simpRelat (e , m , n , s , w) 
    |   m <= n      =   (e , m , n , s , w)
    |   otherwise   =   (reverseMR e , n , m , s , w)

-- ====================================================
-- Basic text processing utility
untilC :: Char -> String -> Maybe (String , String)
untilC _ [] = Nothing
untilC c (d : s)
    |   c == d      =   Just ([] , s)
    |   otherwise   =   untilC c s >>= \(x , y) -> Just (d : x , y) 

-- Parse next word: that is bit between spaces 
parseWord :: String -> (String , String)
parseWord [] = ("" , "")
parseWord (' ' : s) = parseWord s
parseWord (c : s) = case untilC ' ' (c : s) of 
    Just (a , b)    ->  (a , b)
    Nothing         ->  (c : s , "")

-- Extracting content between brackets: can input bracket symbols
parseBrack :: Char -> Char -> String -> Maybe (String , String)
parseBrack l r s = untilC l s >>= \(_ , z) -> parseBrack' l r 0 z

parseBrack' :: Char -> Char -> Int -> String -> Maybe (String , String)
parseBrack' _ _ _ [] = Nothing
parseBrack' l r i (c : s)
    |   l == c              =   fmap (first (c :)) (parseBrack' l r (i+1) s)
    |   r == c && i == 0    =   Just ([] , s)
    |   r == c              =   fmap (first (c :)) (parseBrack' l r (i-1) s)
    |   otherwise           =   fmap (first (c :)) (parseBrack' l r i s)

-- NUMBER PARSER 
parseNum :: String -> Maybe (Int , String)
parseNum = parseNum' 0

parseNum' :: Int -> String -> Maybe (Int , String)
parseNum' x []          =   Just (x , [])
parseNum' x ('0' : s)   =   parseNum' (x*10) s
parseNum' x ('1' : s)   =   parseNum' (x*10+1) s
parseNum' x ('2' : s)   =   parseNum' (x*10+2) s
parseNum' x ('3' : s)   =   parseNum' (x*10+3) s
parseNum' x ('4' : s)   =   parseNum' (x*10+4) s
parseNum' x ('5' : s)   =   parseNum' (x*10+5) s
parseNum' x ('6' : s)   =   parseNum' (x*10+6) s
parseNum' x ('7' : s)   =   parseNum' (x*10+7) s
parseNum' x ('8' : s)   =   parseNum' (x*10+8) s
parseNum' x ('9' : s)   =   parseNum' (x*10+9) s
parseNum' x (' ' : s)   =   parseNum' x s
parseNum' x (c : s)     =   Just (x , c : s)

-- CHARACTER PARSER 
parseChar :: String -> Maybe (Char , String)
parseChar (' ' : s) = parseChar s
parseChar (c : s) = Just (c , s)
parseChar _ = Nothing


nextC :: String -> (Char , String)
nextC [] = (' ' , [])
nextC (' ' : l) = nextC l
nextC (c : l) = (c , l) 

-- ====================================================
parseMR :: Char -> Maybe MR 
parseMR '=' = Just MEqual 
parseMR '<' = Just MLarger 
parseMR '>' = Just MSmaller 
parseMR _ = Nothing

parseShow :: [Sig] -> String -> Maybe (Relat , String)
parseShow sig t = 
    let (name , t1) = parseWord t in 
    parseBrack '(' ')' t1 >>= \(ar , t2) -> 
    parseNum ar >>= \(i , _) -> 
    parseBrack '{' '}' t2 >>= \(content , t3) -> 
    parseMorph sig content (Start i) >>= \(m , _) -> 
        Just ((MEqual , m , m , name , Show) , t3)

parseRelation :: Why -> [Sig] -> String -> Maybe (Relat , String)
parseRelation why sig t = 
    let (name , t1) = parseWord t in 
    parseBrack '(' ')' t1 >>= \(ar , t2) -> 
    parseNum ar >>= \(i , _) -> 
    parseBrack '{' '}' t2 >>= \(content , t3) -> 
    parseMorph sig content (Start i) >>= \(m , content2) -> 
    let (c , content3) = nextC content2 in
    parseMR c >>= \mr -> 
    parseMorph sig content3 (Start i) >>= \(n , _) -> 
        Just ((mr , m , n , name , why) , t3)

parseMorph :: [Sig] -> String -> Morph -> Maybe (Morph , String) 
parseMorph _   [] m = Just (m , [])
parseMorph sig ('i' : 'd' : t) m = parseMorph sig t m
parseMorph sig (' ' : t) m = parseMorph sig t m
parseMorph sig (',' : t) m = parseMorph sig t m
parseMorph _   ('=' : t) m = Just (m , '=' : t)
parseMorph _   ('<' : t) m = Just (m , '<' : t)
parseMorph _   ('>' : t) m = Just (m , '>' : t)
parseMorph sig (c : t) m = 
    untilC ':' (c : t) >>= \(a , t2) -> 
    parseNum a >>= \(i , _) -> 
    let (d , t3) = nextC t2 in
    case d of 
        '[' ->  parseBrack '[' ']' t2 >>= \(con , t4) -> 
                parseRelation Axiom sig con >>= \((mr , v , w , name , why) , _) -> 
                parseMorph sig t4 (Op m i (Comp (RS mr w name why) v))
        _   ->  lookupSig d sig >>= \(Sig nam (ex , style) io oo) ->
                case ex of 
                    Nothing     ->  parseMorph sig t3 (Op m i (Base (Sig nam (ex , style) io oo)))
                    Just _      ->  parseBrack '(' ')' t3 >>= \(rest' , t4) ->
                                    parseExp rest' >>= \ex' ->
                                    parseMorph sig t4 (Op m i (Base (Sig nam (Just ex' , style) io oo)))
                        
    
parseOper :: String -> Maybe (Sig , String)
parseOper text = 
    let (c , text1) = nextC text in 
    untilC ':' text1 >>= \(_ , text2) -> 
    untilC '-' text2 >>= \(a , text3) -> 
    parseNum a >>= \(a' , _) ->
    untilC '>' text3 >>= \(_ , text4) -> 
    let (b , text5) = parseWord text4 in 
    parseNum b >>= \(b' , _) -> 
    let (d , _) = nextC text5 in
    case d of 
        '['     ->  parseBrack '[' ']' text5 >>= \(style , text6) -> 
                    Just (Sig c (Nothing , style) a' b' , text6) 
        _       ->  Just (Sig c (Nothing , "") a' b' , text5) 
    
parsePruf :: [Sig] -> String -> Maybe (Proof , String)
parsePruf sig text1 = 
    parseBrack '(' ')' text1 >>= \(c1 , text2) -> 
    parseBrack '{' '}' text2 >>= \(c2 , text3) -> 
    parseNum c1 >>= \(a , _) -> 
    parsePruf' sig a c2 >>= \lis -> 
    reconstProof lis >>= \(m , l) ->
        Just ((m , l) , text3)

parsePruf' :: [Sig] -> Int -> String -> Maybe [Morph]
parsePruf' _ _ [] = Just []
parsePruf' sig a (' ' : text) = parsePruf' sig a text
parsePruf' sig a ('=' : text) = parsePruf' sig a text
parsePruf' sig a (c : text)   = parseMorph sig (c : text) (Start a) >>= \(m , text1) -> 
                                fmap (m :) (parsePruf' sig a text1)

poap :: [a] -> Maybe (a , [a])
poap [] = Nothing 
poap (a : l) = Just (a , l) 

fald :: [a] -> Maybe [a]
fald [] = Nothing 
fald l = Just l

parseSchem :: [Sig] -> String -> Maybe (Schema , String)
parseSchem sig text = 
    let (schem , text1) = parseWord text in 
    parseBrack '{' '}' text1 >>= \(s , text2)  ->
    parseOperations' sig s >>= \l ->
    parseBrack '{' '}' text2 >>= \(z , text3)  ->
    parseOperations' sig z >>= \r ->
    case schem of 
        "symmetry"      ->  poap l >>= \(x , _) -> 
                            Just (Symmetry x (fald (sortSet r)) , text3)
        "naturality"    ->  poap l >>= \(x , l2) -> poap l2 >>= \(f , _) -> 
                            Just (Naturality x f MEqual (fald (sortSet r)) , text3)
        "naturality<"   ->  poap l >>= \(x , l2) -> poap l2 >>= \(f , _) -> 
                            Just (Naturality x f MLarger (fald (sortSet r)) , text3)
        "naturality>"   ->  poap l >>= \(x , l2) -> poap l2 >>= \(f , _) -> 
                            Just (Naturality x f MSmaller (fald (sortSet r)) , text3)
        "if"            ->  poap l >>= \(x , l2) -> poap l2 >>= \(c , l3) -> poap l3 >>= \(d , l4) -> poap l4 >>= \(p , l4) -> 
                            Just (If x c d p (fald (sortSet r)) , text3)
        "flip"          ->  Just (Flip (cleanDict (zip l r)) , text3)
        "mirror"        ->  Just (Mirror (cleanDict (zip l r)) , text3)
        "toggle"        ->  Just (Toggle (cleanDict (zip l r)) , text3)
        _               ->  Nothing

-- =====================
    
parseDisp :: Bool -> Int -> [Sig] -> String -> Maybe (Int , [Sig] , [Disp])
parseDisp b t = parseDisp' b t ""

relatBox :: Relat -> Morph 
relatBox (mr , m , n , name , why) = 
    let (a , _) = typeMorph m in 
    Op (Start a) 0 (Comp (RS mr n name why) m)

relatMem :: Relat -> Mem 
relatMem (mr , m , n , name , why) = (m , 1 , (m , [(n , mr , name , why , relatBox (mr , m , n , name , why))]) , Just (n , []))

-- first setting declares whether proofs are loaded
parseDisp' :: Bool -> Int -> String -> [Sig] -> String -> Maybe (Int , [Sig] , [Disp]) 
parseDisp' b c comment sig text = let (word , text1) = parseWord text  in case word of 
    "op"        ->  parseOper text1 >>= \(o , text2) ->      
                    fmap (second (Opera o :)) (parseDisp' b c comment (sig ++ [o]) text2)
    "lem"       ->  parseRelation Lemma sig text1 >>= \(rel , text2) -> 
                    fmap (second ([Displ rel Nothing comment , Assum rel] ++)) (parseDisp' b (c+1) "" sig text2)
    "lem-hide"  ->  parseRelation Lemma sig text1 >>= \(rel , text2) -> 
                    fmap (second (Assum rel :)) (parseDisp' b (c+1) comment sig text2)
    "def"       ->  parseRelation Axiom sig text1 >>= \(rel , text2) -> 
                    fmap (second ([Assum rel , Displ rel (Just (relatMem rel)) comment ] ++)) (parseDisp' b (c+1) "" sig text2)
    "def-hide"  ->  parseRelation Axiom sig text1 >>= \(rel , text2) ->
                    fmap (second (Assum rel :)) (parseDisp' b (c+1) comment sig text2)
    "show"      ->  parseShow sig text1 >>= \(rel , text2) -> 
                    fmap (second (Displ rel Nothing comment :)) (parseDisp' b (c+1) "" sig text2)
    "note"      ->  parseName text1 >>= \(s , text2) ->
                    parseDisp' b c s sig text2
    "example"   ->  parseRelation Lemma sig text1 >>= \(rel , text2) -> 
                    fmap (second (Displ rel Nothing comment :)) (parseDisp' b (c+1) "" sig text2)
    "proof"     ->  parsePruf sig text1 >>= \(p , text2) -> 
                    if b then fmap (second (Displ (proofRelat p) (Just (proofMem p)) comment :)) (parseDisp' b c "" sig text2)
                         else parseDisp' b c "" sig text2
    "schema"    ->  parseSchem sig text1 >>= \(schem , text2) ->
                    fmap (second (Schem schem :)) (parseDisp' b c "" sig text2)
    _           ->  case popChar text of
        -- Name Buffer
        Just ('N' , text2)  ->  parseName text2 >>= \(s , text3) ->
                                parseDisp' b c s sig text3
        -- Operation
        Just ('O' , text2)  ->  parseSig text2 >>= \(s , text3) ->
                            fmap (second (Opera s :)) (parseDisp' b c comment (sig ++ [s]) text3)
        -- ! Displayed Definition 
        Just ('D' , text2)  ->  parseRelat (sms' ("Axiom" ++ show c) comment) Axiom sig text2 >>= \(rel , text3) ->
                            fmap (second ([Assum rel , Displ rel (Just (relatMem rel)) comment ] ++)) (parseDisp' b (c+1) "" sig text3)
        -- Assumption, not displayed
        Just ('A' , text2)  ->  parseRelat (sms' ("Axiom" ++ show c) comment) Axiom sig text2 >>= \(rel , text3) ->
                            fmap (second (Assum rel :)) (parseDisp' b (c+1) "" sig text3)
        -- Lemma 
        Just ('L' , text2)  ->  parseRelat (sms' ("Lemma" ++ show c) comment) Lemma sig text2 >>= \(rel , text3) ->
                            fmap (second ([Displ rel Nothing comment , Assum rel] ++)) (parseDisp' b (c+1) "" sig text3)
        Just ('V' , text2)  ->  parseRelat (sms' ("Lemma" ++ show c) comment) Lemma sig text2 >>= \(rel , text3) ->
                            fmap (second (Assum rel :)) (parseDisp' b (c+1) "" sig text3)
        -- ! Example
        Just ('E' , text2)  ->  parseRelat (sms' ("Example" ++ show c) comment) Lemma sig text2 >>= \(rel , text3) ->
                            fmap (second (Displ rel Nothing comment :)) (parseDisp' b (c+1) "" sig text3)
        -- Play (open ended display)
        Just ('P' , text2)  ->  parseMorphOnly (sms' ("Open" ++ show c) comment) Lemma sig text2 >>= \(rel , text3) ->
                            fmap (second (Displ rel Nothing comment :)) (parseDisp' b (c+1) "" sig text3)
        -- Trace proof 
        Just ('T' , text2)  ->  parseProof sig text2 >>= \(p , text3) -> 
                            if b then 
                                fmap (second (Displ (proofRelat p) (Just (proofMem p)) comment :)) (parseDisp' b c "" sig text3)
                            else 
                                parseDisp' b c "" sig text3
        -- Schema (adds relevant schema relations)
        Just ('S' , text2)  ->  parseSchema sig text2 >>= \(t , text3) ->
                            fmap (second (Schem t :)) (parseDisp' b c "" sig text3)
        -- Basic relation (adds relevant schema relations)
        Just ('B' , text2)  ->  parseBasic sig text2 >>= \(t , text3) ->
                            fmap (second (fmap Assum (newBasic t) ++ )) (parseDisp' b (c+1) "" sig text3)
        _                   ->  Just (c , sig , [])


-- IMPORT STRUCTURE
parseDLoc :: Bool -> Int -> [String] -> String -> [Sig] -> IO (Int , [Sig] , [Disp] , [Disp] , [String])
parseDLoc b c struc file sig
    |   inList file struc   =   return (c , sig , [] , [] , struc)
    |   otherwise           =   readFile ("input/" ++ file ++ ".txt") >>= \s ->
                                let z = strip s in 
                                parseDFile b c (file : struc) sig z -- >>= \(c' , sig' , disp1' , disp2' , struc') -> return (c' , sig' , disp1' , disp2' , struc')

parseDFile :: Bool -> Int -> [String] -> [Sig] -> String ->  IO (Int , [Sig] , [Disp] , [Disp] , [String])
parseDFile b c struc sig text =    case popChar text of
    Just ('I' , text2)  ->  case parseBrack '{' '}' text2 of
        Just (file , text3) ->  parseDLoc False c struc file sig >>= \(c' , sig' , disp1' , disp2' , struc') ->
                parseDFile b c' struc' sig' text3 >>= \(c'' , sig'' , disp1'' , disp2'' , struc'')  ->  
                    return (c'' , sig'' , disp1' ++ disp2' ++ disp1'' , disp2'' , struc'')
        _                   ->  return (c , [] , [] , [] , struc)
    Just ('i' , _)  ->  let (_ , text2) = parseWord text in let (file , text3) = parseWord text2 in
                parseDLoc False c struc file sig >>= \(c' , sig' , disp1' , disp2' , struc') ->
                parseDFile b c' struc' sig' text3 >>= \(c'' , sig'' , disp1'' , disp2'' , struc'')  ->  
                return (c'' , sig'' , disp1' ++ disp2' ++ disp1'' , disp2'' , struc'')
    Just (d , text2)    ->  case parseDisp b c sig (d : text2) of 
        Just (c' , sig' , disp')    ->  return (c' , sig' , [] , disp' , struc)  
        _                           ->  return (c , [] , [] , [] , struc)
    Nothing             ->  return (c , [] , [] , [] , struc)


-- Information of current "page" in the loaded document
--          current relation
--                  current theory
--                          next assertions
--                                  previous assertions  
--                                      comment          
--                                                      file
type Page = (Relat, Maybe Mem , Theor,  [Disp], [Disp] , String , String)

pagePar :: Page -> Par Morph 
pagePar (_ , _ , (_ , _ , _ , par) , _ , _ , _ , _) = par

pageSig :: Page -> [Sig]
pageSig (_ , _ , (sig , _ , _ , _) , _ , _ , _ , _) = sig

initPage :: Bool -> String -> IO Page 
initPage b file = 
    parseDLoc b 0 [] file [] >>= \(_ , _ , disp1 , disp2 , _) -> 
    let t = theorySteps ([] , [] , [] , []) disp1 in 
    return (newSteps t disp2 (reverse disp1) file)

nextPage :: Page -> Page 
nextPage (_ , v ,t , d1 , d2 , _ , file) = newSteps t d1 (setMemory v d2) file

-- go back through history to the last display, and regenerate state for this
previousPage :: Page -> Page 
previousPage (r , v ,t , d1 , d2 , comment , file) = 
    let d2' = setMemory v d2 in
    case popDisp d2' of 
    Nothing             ->  (r , v , t , d1 , d2' , comment , file)
    Just (d21 , z , d22)    ->  let t' = theorySteps ([] , [] , [] , []) (reverse d22) in 
        newSteps t' (z : reverse d21 ++ d1) d22 file


-- introducing a duplicate operation removes all prior equations mentioning the previous one.
newStep :: Theor -> [Disp] -> [Disp] -> (Theor , [Disp] , [Disp] , Maybe (Relat , Maybe Mem , String))
newStep t [] his = (t , [] , Displ (MEqual , Start 0 , Start 0 , "End" , Axiom) Nothing "" : his , Just ((MEqual , Start 0 , Start 0 , "End" , Axiom) , Nothing , ""))
newStep theor (Opera s : l) his = 
    let Sig c _ _ _ = s in
    let (sigs , schem , rel , par) = flushTheor c theor in
    let relat = sieveRelat (newOp schem s) in 
    ((sigs ++ [s] , schem  , filterAdd' relat rel , addRelatsPar relat par) , l , Opera s : his , Nothing)
newStep (sigs , schem , rel , par) (Schem s : l) his = 
    let (s' , schem') = addSchema s schem in
    let relat = sieveRelat (newSchema s' sigs ++ newSchema2 s' rel) in
    ((sigs , schem' , filterAdd' relat rel , addRelatsPar relat par)  , l , Schem s' : his , Nothing)
newStep (sigs , schem , rel , par) (Assum s : l) his = 
    let relat = sieveRelat (s : newRelats schem [s]) in
    ((sigs , schem , filterAdd' relat rel , addRelatsPar relat par)  , l , Assum s : his , Nothing)
newStep (sigs , schem , rel , par) (Displ s v c : l) his = ((sigs , schem , rel , par)  , l , Displ s v c : his , Just (s , v , c))

newSteps :: Theor -> [Disp] -> [Disp] -> String -> Page
newSteps t disp1 disp2 file = 
    let (t' , disp1' , disp2' , x) = newStep t disp1 disp2 in 
    case x of 
        Just (rel , v , comment)    ->  (rel , v , t' , disp1' , disp2' , comment , file)
        Nothing                     ->  newSteps t' disp1' disp2' file

theorySteps :: Theor -> [Disp] -> Theor 
theorySteps t [] = t 
theorySteps t l = let (t' , l' , _ , _) = newStep t l [] in theorySteps t' l'

popDisp :: [Disp] -> Maybe ([Disp] , Disp , [Disp])
popDisp [] = Nothing 
popDisp [_] = Nothing 
popDisp (x : Opera s : l) = popDisp (Opera s : l) >>= \(d1 , z , d2) -> Just (x : d1 , z , d2)
popDisp (x : Schem s : l) = popDisp (Schem s : l) >>= \(d1 , z , d2) -> Just (x : d1 , z , d2)
popDisp (x : Assum s : l) = popDisp (Assum s : l) >>= \(d1 , z , d2) -> Just (x : d1 , z , d2)
popDisp (x : Displ s v c : l) = Just ([x] , Displ s v c , l)

isEnd :: Relat -> Bool 
isEnd (MEqual , Start 0 , Start 0 , "End" , Axiom) = True 
isEnd _ = False

setMemory :: Maybe Mem -> [Disp] -> [Disp]
setMemory (Just viv) (Displ s _ c : l) = Displ s (Just viv) c : l 
setMemory _ l = l

toss :: a -> [a] -> [a]
toss a [] = [a]
toss a (b : l) = b : a : l

-- ===============================================
-- Parsing text from a file to extract information
-- ===============================================

firstelem :: a -> [a] -> a
firstelem a [] = a
firstelem _ (b : _) = b

popelem :: a -> [a] -> (a , [a])
popelem a [] = (a , [])
popelem _ (b : c) = (b , c)



-- Removing comments
strip :: String -> String
strip s = stripComment False (stripNewline s)

stripComment :: Bool -> String -> String
stripComment _ [] = []
stripComment k ('#' : s) = stripComment (not k) s
stripComment True (_ : s) = stripComment True s
stripComment False (c : s) = c : stripComment False s

-- Removing linebreaks
stripNewline :: String -> String
stripNewline [] = []
stripNewline ('\n' : s) = ' ' : stripNewline s
stripNewline ('\r' : s) = ' ' : stripNewline s
stripNewline ('\t' : s) = ' ' : stripNewline s
--stripNewline (' ' : s) = stripNewline s
stripNewline (c : s) = c : stripNewline s




popChar :: String -> Maybe (Char, String)
popChar (' ' : s) = popChar s
popChar (c : s) = Just (c , s)
popChar _ = Nothing

-- Parsing numbers
numParse' :: Char -> Maybe Int
numParse' '0' = Just 0
numParse' '1' = Just 1
numParse' '2' = Just 2
numParse' '3' = Just 3
numParse' '4' = Just 4
numParse' '5' = Just 5
numParse' '6' = Just 6
numParse' '7' = Just 7
numParse' '8' = Just 8
numParse' '9' = Just 9
numParse' _ = Nothing

isNum :: Char -> Bool 
isNum c = inList c "0123456789"

untilNonnum :: String -> (String , String)
untilNonnum [] = ([] , [])
untilNonnum (c : l) 
    |   isNum c     =   let (x , y) = untilNonnum l in (c : x , y)
    |   otherwise   =   ([] , c : l)



-- NAME PARSER
parseName :: String -> Maybe (String , String)
parseName =
    parseBrack '{' '}'


-- SIGNATURE PARSER
parseSig :: String -> Maybe (Sig , String)
parseSig text =
    parseBrack '{' '}' text  >>= \(c' , text2)  ->  parseChar c' >>= \(c , _) ->
    parseBrack '{' '}' text2 >>= \(s  , text3)  ->
    parseBrack '{' '}' text3 >>= \(i' , text4)  ->  parseNum i' >>= \(i , _) ->
    parseBrack '{' '}' text4 >>= \(o' , text5)  ->  parseNum o' >>= \(o , _) ->
        case s of 
            ('%' : s')  ->  Just (Sig c (Just (linExp 'X' 0) , s') i o , text5)
            _           ->  Just (Sig c (Nothing , s) i o , text5)

parseMono :: String -> Maybe (Mono Char)
parseMono [] = Just (0 , [])
parseMono l =   let (a , b) = untilNonnum l in 
                case a of 
                    []  ->  Just (cleanMono (1 , b))
                    _   ->  parseNum a >>= \(i , _) -> Just (cleanMono (i , b))

parsePoly :: String -> Maybe (Poly Char)
parsePoly [] = Just []
parsePoly l = case untilC '+' l of 
    Just (a , b)    ->  parseMono a >>= \mon -> parsePoly b >>= \pol -> Just (addMono mon pol)
    _               ->  parseMono l >>= \mon -> Just (cleanPoly [mon])

-- EXPRESSION PARSER (TEMPORARY, MUST FIX)
parseExp :: String -> Maybe Exp 
parseExp s = parsePoly s >>= \pol -> Just (Pol pol)
-- parseExp [] = Just (constExp 0)
-- parseExp (c : '+' : l) = parseNum l >>= \(i , _) -> Just (linExp c i)
-- parseExp (c : l) = case numParse' c of 
--     Just _      ->  parseNum (c : l) >>= \(i , _) -> Just (constExp i)
--     _           ->  Just (linExp c 0)  

-- MORPHISM PARSER
parseMorphism :: [Sig] -> Int -> String -> Maybe (Morph , String)
parseMorphism sig i = parseMorphism' sig (Start i)

-- To fix: need to parse ";" better, allow using it within {---}
parseMorphism' :: [Sig] -> Morph -> String -> Maybe (Morph , String)
parseMorphism' sig base text =
    case untilC ';' text of
        Nothing             ->  Just (base , text)
        Just (now , _)    ->  
            untilC '.' text  >>= \(i' , text2)  ->
            parseNum i'     >>= \(i  , _ )  ->
            parseChar text2    >>= \(c  , text3 )->
            if c == '{' then 
                parseComp sig text2 >>= \(m , n , name , mr , text4) -> 
                untilC ';' text4 >>= \(_ , text5) ->
                --Just (m , "cheese")
                parseMorphism' sig (Op base i (Comp (RS mr n name Axiom) m)) text5  
            else
                lookupSig c sig >>= \(Sig nam (ex , style) a b) ->
                untilC ';' text3 >>= \(_ , text4) ->
                case ex of 
                    Nothing  -> 
                        parseMorphism' sig (Op base i (Base (Sig nam (Nothing , style) a b))) text4
                    Just _   ->  
                        parseBrack '{' '}' text3 >>= \(rest' , _) ->
                        parseExp rest' >>= \ex' ->
                        parseMorphism' sig (Op base i (Base (Sig nam (Just ex' , style) a b))) text4



parseProof :: [Sig] -> String -> Maybe (Proof , String)
parseProof sig text1 = 
    parseBrack '{' '}' text1 >>= \(c1 , text2) -> 
    parseBrack '{' '}' text2 >>= \(c2 , text3) -> 
    parseNum c1 >>= \(a , _) -> 
    parseProof' sig a c2 >>= \lis -> 
    reconstProof lis >>= \(m , l) ->
        Just ((m , l) , text3)
        --Just (p , text3)


parseProof' :: [Sig] -> Int -> String -> Maybe [Morph]
parseProof' sig i text = 
    case untilC '|' text of 
        Just (text1 , text2) -> 
            parseMorphism sig i text1 >>= \(m , _) ->
            parseProof' sig i text2 >>= \p -> 
                Just (m : p)
        Nothing -> 
            parseMorphism sig i text >>= \(m , _) ->
                Just [m]

parseComp :: [Sig] -> String -> Maybe (Morph , Morph , String , MR , String)
parseComp sig text1 = 
    parseBrack '{' '}' text1 >>= \(c1 , text2) ->
    parseBrack '{' '}' text2 >>= \(c2 , text3) ->
    parseBrack '{' '}' text3 >>= \(c3 , text4) ->
    parseChar text4          >>= \(c4 , text5) -> 
    parseBrack '{' '}' text5 >>= \(c5 , text6) ->
    parseNum c1 >>= \(a , _) -> 
    parseMorphism sig a c3 >>= \(m , _) ->
    parseMR c4 >>= \mr ->
    parseMorphism sig a c5 >>= \(n , _) ->
        Just (m , n , c2 , mr , text6)
    --    Just (Start 7 , Start 9 , "Cheese" , MEqual , text6)

-- OPERATION LIST PARSER 
parseOperations :: [Sig] -> String -> Maybe [Sig]
parseOperations _ [] = Just []
parseOperations sig (c : text) =
    lookupSig c sig >>= \o ->
    case untilC '.' text of
        Just (_ , text2)    ->  fmap (o:) (parseOperations sig text2)
        _                   ->  Just [o]

parseOperations' :: [Sig] -> String -> Maybe [Sig]
parseOperations' _ [] = Just []
parseOperations' sig (' ' : text) = parseOperations' sig text
parseOperations' sig (c : text) =
    lookupSig c sig >>= \o ->
    case untilC ',' (c : text) of
        Just (_ , text2)    ->  fmap (o:) (parseOperations' sig text2)
        _                   ->  Just [o]

-- RELATION PARSER 
parseRelat :: String -> Why -> [Sig] -> String -> Maybe (Relat , String)
parseRelat s w sig text =
    parseBrack '{' '}' text  >>= \(i' , text2)  ->  parseNum i'             >>= \(i , _) ->
    parseBrack '{' '}' text2 >>= \(m' , text3)  ->  parseMorphism sig i m'  >>= \(m , _) ->
    parseBrack '{' '}' text3 >>= \(n' , text4)  ->  parseMorphism sig i n'  >>= \(n , _) ->
        case text3 of
            ('<' : _)   ->  Just ((MLarger , m , n , s , w) , text4)
            ('>' : _)   ->  Just ((MSmaller , m  , n , s , w) , text4)
            _           ->  Just ((MEqual , m , n , s , w) , text4)

-- RELATION PARSER 
parseMorphOnly :: String -> Why -> [Sig] -> String -> Maybe (Relat , String)
parseMorphOnly s w sig text =
    parseBrack '{' '}' text  >>= \(i' , text2)  ->  parseNum i'             >>= \(i , _) ->
    parseBrack '{' '}' text2 >>= \(m' , text3)  ->  parseMorphism sig i m'  >>= \(m , _) ->
        case text3 of
            ('<' : _)   ->  Just ((MLarger , m , m , s , w) , text3)
            ('>' : _)   ->  Just ((MSmaller , m  , m , s , w) , text3)
            _           ->  Just ((MEqual , m , m , s , w) , text3)


-- BASIC RELATION PARSER
parseBasic :: [Sig] -> String -> Maybe (Basic , String)
parseBasic sig text =
    parseBrack '{' '}' text  >>= \(t' , text2)  ->
    parseBrack '{' '}' text2 >>= \(s' , text3)  ->
    case t' of
        ('s' : _)       ->  case parseOperations sig s' of
            Just [x , s]    ->  Just (Swap x s , text3)
            _               ->  Nothing
        ('<' : 'd' : _)       ->  case parseOperations sig s' of
            Just [x,f,g]    ->  Just (Dist x f g MLarger , text3)
            _               ->  Nothing
        ('>' : 'd' : _)       ->  case parseOperations sig s' of
            Just [x,f,g]    ->  Just (Dist x f g MSmaller , text3)
            _               ->  Nothing
        ('d' : _)       ->  case parseOperations sig s' of
            Just [x,f,g]    ->  Just (Dist x f g MEqual , text3)
            _               ->  Nothing
        _               ->  Nothing

-- THEORY PARSER 
parseSchema :: [Sig] -> String -> Maybe (Schema , String)
parseSchema sig text =
    parseBrack '{' '}' text  >>= \(t' , text2)  ->
    parseBrack '{' '}' text2 >>= \(s' , text3)  ->
    parseBrack '{' '}' text3 >>= \(l' , text4)  ->
    case t' of
        ('s' : _)       ->  parseChar s' >>= \(s , _) ->
                            lookupSig s sig >>= \op ->
                            parseOperations sig l' >>= \l ->
                            if null l then
                                Just (Symmetry op Nothing, text4)
                            else
                                Just (Symmetry op (Just (sortSet l)), text4)
        ('<' : 'n' : _)       ->  case parseOperations sig s' of
            Just [x,f]      ->  parseOperations sig l' >>= \l ->
                                if null l then
                                    Just (Naturality x f MLarger Nothing, text4)
                                else
                                    Just (Naturality x f MLarger (Just (sortSet l)), text4)
            _               ->  Nothing
        ('>' : 'n' : _)       ->  case parseOperations sig s' of
            Just [x,f]      ->  parseOperations sig l' >>= \l ->
                                if null l then
                                    Just (Naturality x f MSmaller Nothing, text4)
                                else
                                    Just (Naturality x f MSmaller (Just (sortSet l)), text4)
            _               ->  Nothing
        ('n' : _)       ->  case parseOperations sig s' of
            Just [x,f]      ->  parseOperations sig l' >>= \l ->
                                if null l then
                                    Just (Naturality x f MEqual Nothing, text4)
                                else
                                    Just (Naturality x f MEqual (Just (sortSet l)), text4)
            _               ->  Nothing
        ('i' : _)       ->  case parseOperations sig s' of
            Just [x,c,d,p]  ->  parseOperations sig l' >>= \l ->
                                if null l then
                                    Just (If x c d p Nothing, text4)
                                else
                                    Just (If x c d p (Just (sortSet l)), text4)
            _               ->  Nothing
        ('f' : _)       ->  parseOperations sig s' >>= \x -> parseOperations sig l' >>= \y -> Just (Flip (cleanDict (zip x y)) , text4)
        ('m' : _)       ->  parseOperations sig s' >>= \x -> parseOperations sig l' >>= \y -> Just (Mirror (cleanDict (zip x y)) , text4)
        ('t' : _)       ->  parseOperations sig s' >>= \x -> parseOperations sig l' >>= \y -> Just (Toggle (cleanDict (zip x y)) , text4)
        _               ->  Nothing


sms :: String -> Maybe String -> String
sms s Nothing = s
sms _ (Just s) = s

sms' :: String -> String -> String
sms' s "" = s 
sms' _ z = uptoBar z 
