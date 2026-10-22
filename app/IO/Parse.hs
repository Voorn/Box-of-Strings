{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Replace case with fromMaybe" #-}
{-# LANGUAGE InstanceSigs #-}
module IO.Parse where

-- standard libraries
import Data.Bifunctor
import Data.Ratio
import System.Directory

-- in project libraries
import Theory.Matcher
import Morph
--import Rewrite
import Theory.Theory
import Theory.Par2
import Proof

type Mem = (Morph , Int , SprawlProof , Maybe SprawlProof)


data Error a =
    Cor a
    |   Err String

instance Functor Error where
    fmap :: (a -> b) -> Error a -> Error b
    fmap f (Cor a) = Cor (f a) 
    fmap _ (Err s) = Err s

instance Applicative Error where
    pure :: a -> Error a
    pure = Cor
  
    (<*>) :: Error (a -> b) -> Error a -> Error b
    (<*>) (Err s) _ = Err s
    (<*>) _ (Err s) = Err s
    (<*>) (Cor f) (Cor a) = Cor (f a)

instance Monad Error where
    (>>=) :: Error a -> (a -> Error b) -> Error b
    (>>=) (Err s) _ = Err s
    (>>=) (Cor a) f = f a


-- instance Monad Error where
--  (>>=) :: Error a -> (a -> Error b) -> Error b
--  (>>=) = _

skip :: String
skip = " \n\t\r"

proofMem :: SprawlProof -> Mem 
proofMem (m , l) = (m , 0 , (m , l) , Just (sprawlGoal (m , l) , Spra []))

data LP =
    Nop 
    |   Yep Proof Bool String
    deriving (Eq , Show)

-- attempt to clean up a bit
-- Display instructions: concrete step for what to add and what to display
data Disp = Opera Sig String
        |   Schem Schema String
        |   Assum Relat String
-- Relat: relation with name and reason, LP: proof loaded?, Mem: current history, String: note, Bool: show or hidden, String: file text
        |   Displ Relat LP (Maybe Mem) String Bool String   
        |   Initi String String
    deriving Show

dispLemma :: Disp -> Maybe Relat
dispLemma (Displ (mr , m , n , name , Lemma) _ _ _ _ _) = Just (mr , m , n , name , Lemma)
dispLemma _ = Nothing

dispAxiom :: Disp -> Maybe Relat
dispAxiom (Displ (mr , m , n , name , Axiom) _ _ _ _ _) = Just (mr , m , n , name , Axiom)
dispAxiom _ = Nothing

-- A theory contains a signature, as list of schema, and a data structure of relations
type Theor = ([Sig] , [Schema] , [Relat] , Par Morph)

-- flushing operations removes any mention of a certain operation
flushRelat :: String -> [Relat] -> [Relat]
flushRelat _ [] = []
flushRelat c ((moder, m , n , name , w) : l) 
    |   opinMorph c m || opinMorph c n  =   flushRelat c l
    |   otherwise                       =   (moder, m , n , name , w) : flushRelat c l

flushTheor :: String -> Theor -> Theor 
flushTheor c (sigs , schem , relat , par) = (flushSig c sigs , flushSchema c schem , flushRelat c relat , flushPar c par)

cleaneq :: Morph -> Morph -> Bool 
cleaneq m n = cleanMorph m == cleanMorph n

filterAdd :: Relat -> [Relat] -> [Relat]
filterAdd a [] = [a]
filterAdd (x , a , b , p , w) ((y , c , d , q , v) : l)
    |   orderMR y x && cleaneq a c && cleaneq b d               =   (y , c , d , q , v) : l
    |   orderMR y (reverseMR x) && cleaneq b c && cleaneq a d   =   (y , c , d , q , v) : l
    |   otherwise                                               =   (y , c , d , q , v) : filterAdd (x , a , b , p , w) l

filterAdd' :: [Relat] -> [Relat] -> [Relat]
filterAdd' l r = foldl (flip filterAdd) r l

simpRelat :: Relat -> Relat 
simpRelat (e , m , n , s , w) 
    |   m <= n      =   (e , m , n , s , w)
    |   otherwise   =   (reverseMR e , n , m , s , w)

-- ====================================================
-- Basic text processing utility
untilC :: String -> Char -> String -> Error (String , String , String)
untilC acc c [] = Err ("Looking for character: " ++ c : " , in text: " ++ acc)
untilC acc c (d : s)
    |   c == d          =   pure ([] , s , acc ++ [d])
    |   inList d skip   =   untilC (acc ++ [d]) c s
    |   otherwise       =   untilC (acc ++ [d]) c s >>= \(x , y , ac') -> pure (d : x , y , ac') 

untilSkip :: String -> (String , String)
untilSkip [] = ([] , [])
untilSkip (c : l)
    |   inList c ('#' : skip)   =   ([] , c : l)
    |   otherwise       =   let (a , b) = untilSkip l in (c : a , b) 

endComment :: String -> (String , String)
endComment [] = ([] , [])
endComment ('#' : s) = ("#" , s)
endComment (c : s) = let (a , b) = endComment s in (c : a , b)

-- Parse next word: that is bit between spaces 
parseWord :: String -> String -> (String , String , String)
parseWord acc [] = ("" , "" , acc)
parseWord acc ('#' : s) =   let (a , b) = endComment s in parseWord (acc ++ "#" ++ a) b
parseWord acc (c : s)  
    |   inList c skip   =   parseWord (acc ++ [c]) s   
    |   otherwise       =   let (a , b) = untilSkip (c : s) in 
                            (a , b , acc ++ a)

-- Extracting content between brackets: can input bracket symbols
parseBrack :: String -> Char -> Char -> String -> Error (String , String , String)
parseBrack acc l r s = untilC acc l s >>= \(_ , z , acc') -> parseBrack' acc' l r 0 z

parseBrack' :: String -> Char -> Char -> Int -> String -> Error (String , String , String)
parseBrack' acc l _ _ [] = Err ("Could not close bracket: " ++ l : " , in text: " ++ acc)
parseBrack' acc l r i (c : s)
    |   inList c "\n\t"     =   parseBrack' (acc ++ [c]) l r i s
    |   l == c              =   fmap (\(x , y , z) -> (c : x , y , z)) (parseBrack' (acc ++ [c]) l r (i+1) s)
    |   r == c && i == 0    =   pure ([] , s , acc ++ [c])
    |   r == c              =   fmap (\(x , y , z) -> (c : x , y , z)) (parseBrack' (acc ++ [c]) l r (i-1) s)
    |   otherwise           =   fmap (\(x , y , z) -> (c : x , y , z)) (parseBrack' (acc ++ [c]) l r i s)

-- NUMBER PARSER 
parseNum :: String -> String -> (Int , String , String)
parseNum acc = parseNum' acc 0

parseNum' :: String -> Int -> String -> (Int , String , String)
parseNum' acc x []          =   (x , [] , acc)
parseNum' acc x ('0' : s)   =   parseNum' (acc ++ "0") (x*10) s
parseNum' acc x ('1' : s)   =   parseNum' (acc ++ "1") (x*10+1) s
parseNum' acc x ('2' : s)   =   parseNum' (acc ++ "2") (x*10+2) s
parseNum' acc x ('3' : s)   =   parseNum' (acc ++ "3") (x*10+3) s
parseNum' acc x ('4' : s)   =   parseNum' (acc ++ "4") (x*10+4) s
parseNum' acc x ('5' : s)   =   parseNum' (acc ++ "5") (x*10+5) s
parseNum' acc x ('6' : s)   =   parseNum' (acc ++ "6") (x*10+6) s
parseNum' acc x ('7' : s)   =   parseNum' (acc ++ "7") (x*10+7) s
parseNum' acc x ('8' : s)   =   parseNum' (acc ++ "8") (x*10+8) s
parseNum' acc x ('9' : s)   =   parseNum' (acc ++ "9") (x*10+9) s
parseNum' acc x (' ' : s)   =   parseNum' (acc ++ " ") x s
parseNum' acc x ('\n' : s)  =   parseNum' (acc ++ "\n") x s
parseNum' acc x ('\t' : s)  =   parseNum' (acc ++ "\t") x s
parseNum' acc x (c : s)     =   (x , c : s , acc)

-- CHARACTER PARSER 
parseChar :: String -> String -> Maybe (Char , String , String)
parseChar acc (c : s) 
    |   inList c skip    =   parseChar (acc ++ [c]) s
    |   otherwise       =   Just (c , s , acc ++ [c])
parseChar _ _ = Nothing


nextC :: String -> String -> (Char , String , String)
nextC acc [] = (' ' , [] , acc)
nextC acc (c : l) 
    |   inList c skip   =   nextC (acc ++ [c]) l
    |   otherwise       =   (c , l , acc ++ [c]) 

nextWord :: String -> String -> (String , String , String)
nextWord acc [] = ([] , [] , acc)
nextWord acc (c : l)
    |   inList c skip
            =   nextWord (acc ++ [c]) l
    |   inList c "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
            =   let (a , b , acc') = nextWord (acc ++ [c]) l in (c : a , b , acc')
    |   otherwise  
            =   ([] , c : l , acc)

-- ====================================================
parseMR :: Char -> Error MR 
parseMR '=' = pure MEqual 
parseMR '<' = pure MLarger 
parseMR '>' = pure MSmaller 
parseMR c = Err ("Was expectin =, <, or >, but found: " ++ [c])

parseShow :: String -> [Sig] -> String -> Error (Relat , String , String)
parseShow acc sig t = 
    let (name , t1 , acc1) = parseWord acc t in 
    parseBrack acc1 '(' ')' t1 >>= \(ar , t2 , acc2) -> 
    let (i , _ , _) = parseNum "" ar in
    parseBrack acc2 '{' '}' t2 >>= \(content , t3 , acc3) -> 
    parseMorph sig content (Start i) >>= \(m , _) -> 
        pure ((MEqual , m , m , name , Show) , t3 , acc3)

parseRelation :: String -> Why -> [Sig] -> String -> Error (Relat , String , String)
parseRelation acc why sig t = 
    let (name , t1 , acc1) = parseWord acc t in 
    parseBrack acc1 '(' ')' t1 >>= \(ar , t2 , acc2) -> 
    let (i , _ , _) = parseNum "" ar in 
    parseBrack acc2 '{' '}' t2 >>= \(content , t3 , acc3) -> 
    parseMorph sig content (Start i) >>= \(m , content2) -> 
    let (c , content3 , _) = nextC "" content2 in
    parseMR c >>= \mr -> 
    parseMorph sig content3 (Start i) >>= \(n , _) -> 
        pure ((mr , m , n , name , why) , t3 , acc3)

parseFunctor :: String -> [Sig] -> String -> Error (Oper , String , String)
parseFunctor acc sig t = 
    let (name , t1 , acc1) = parseWord acc t in 
    parseBrack acc1 '(' ')' t1 >>= \(ar , t2 , acc2) -> 
    let (i , _ , _) = parseNum "" ar in
    parseBrack acc2 '{' '}' t2 >>= \(content , t3 , acc3) -> 
    parseMorph sig content (Start i) >>= \(m , _) -> 
        pure (Func name m , t3 , acc3)

parseMorph :: [Sig] -> String -> Morph -> Error (Morph , String) 
parseMorph _   [] m = pure (m , [])
parseMorph sig ('i' : 'd' : t) m = parseMorph sig t m
parseMorph sig (',' : t) m = parseMorph sig t m
parseMorph _   ('=' : t) m = pure (m , '=' : t)
parseMorph _   ('<' : t) m = pure (m , '<' : t)
parseMorph _   ('>' : t) m = pure (m , '>' : t)
parseMorph sig (c : t) m 
    |   inList c skip   =   parseMorph sig t m
    |   otherwise       =
            untilC "" ':' (c : t) >>= \(a , t2 , _) -> 
            let (i , _ , _) = parseNum "" a in
            let (d , _ , _) = nextC "" t2 in
            case d of 
        '[' ->  parseBrack "" '[' ']' t2 >>= \(con , t4 , _) -> 
                parseRelation "" Axiom sig con >>= \((mr , v , w , name , why) , _ , _) -> 
                parseMorph sig t4 (Op m i (Comp (RS mr w name why) v))
        '<' ->  parseBrack "" '<' '>' t2 >>= \(con , t4 , _) -> 
                parseFunctor "" sig con >>= \(op , _ , _) -> 
                parseMorph sig t4 (Op m i op)
        _   ->  let (op , t3 , _) = nextWord "" t2 in
                case lookupSig op sig of
                    Nothing     ->  Err ("Reference to no-existent operation: " ++ op)
                    Just (Sig nam (ex , style) io oo) -> case ex of 
                        Nothing     ->  parseMorph sig t3 (Op m i (Base (Sig nam (ex , style) io oo)))
                        Just _      ->  parseBrack "" '(' ')' t3 >>= \(rest' , t4 , _) ->
                                        parseExp rest' >>= \ex' ->
                                        parseMorph sig t4 (Op m i (Base (Sig nam (Just ex' , style) io oo)))
                        
    
parseOper :: String -> String -> Error (Sig , String , String)
parseOper acc text = 
    let (c , text1 , acc1) = nextWord acc text in 
    untilC acc1 ':' text1 >>= \(_ , text2 , acc2) -> 
    untilC acc2 '-' text2 >>= \(a , text3 , acc3) -> 
    let (a' , _ , _) = parseNum "" a in
    untilC acc3 '>' text3 >>= \(_ , text4 , acc4) -> 
    let (b , text5 , acc5) = parseWord acc4 text4 in 
    let (b' , _ , _) = parseNum "" b in
    let (d , _ , _) = nextC "" text5 in
    case d of 
        '['     ->  parseBrack acc5 '[' ']' text5 >>= \(style , text6 , acc6) -> 
                    case style of 
                        ('%' : style')  ->  pure (Sig c (Just (linExp 'X' 0) , style') a' b' , text6 , acc6) 
                        _               ->  pure (Sig c (Nothing , style) a' b' , text6 , acc6) 
                    --pure (Sig c (Nothing , style) a' b' , text6 , acc6) 
        _       ->  pure (Sig c (Nothing , "") a' b' , text5 , acc5) 

parsePruf :: String -> [Sig] -> String -> Error (Proof , String , String)
parsePruf acc1 sig text1 = 
    parseBrack acc1 '(' ')' text1 >>= \(c1 , text2 , acc2) -> 
    parseBrack acc2 '{' '}' text2 >>= \(c2 , text3 , acc3) -> 
    let (a , _ , _) = parseNum "" c1 in
    parsePruf' sig a c2 >>= \lis -> 
    case reconstProof lis of
        Nothing         ->  Err ("Could not construct proof from code: \n" ++ c2)
        Just (m , l)    ->
            pure ((m , l) , text3 , acc3)

parsePruf' :: [Sig] -> Int -> String -> Error [Morph]
parsePruf' _ _ [] = pure []
parsePruf' sig a ('=' : text) = parsePruf' sig a text
parsePruf' sig a (c : text)   
    |   inList c skip   =   parsePruf' sig a text
    |   otherwise       =   parseMorph sig (c : text) (Start a) >>= \(m , text1) -> 
                                fmap (m :) (parsePruf' sig a text1)

poap :: [a] -> Error (a , [a])
poap [] = Err "Not enough operations given" 
poap (a : l) = pure (a , l) 

fald :: [a] -> Maybe [a]
fald [] = Nothing 
fald l = Just l

parseSchem :: String -> [Sig] -> String -> Error (Schema , String , String)
parseSchem acc sig text = 
    let (schem , text1 , acc1) = parseWord acc text in 
    parseBrack acc1 '{' '}' text1 >>= \(s , text2 , acc2)  ->
    parseOperations' sig s >>= \l ->
    parseBrack acc2 '{' '}' text2 >>= \(z , text3 , acc3)  ->
    parseOperations' sig z >>= \r ->
    case schem of 
        "symmetry"      ->  poap l >>= \(x , _) -> 
                            pure (Symmetry x (fald (sortSet r)) , text3 , acc3)
        "naturality"    ->  poap l >>= \(x , l2) -> poap l2 >>= \(f , _) -> 
                            pure (Naturality x f MEqual (fald (sortSet r)) , text3, acc3)
        "naturality<"   ->  poap l >>= \(x , l2) -> poap l2 >>= \(f , _) -> 
                            pure (Naturality x f MLarger (fald (sortSet r)) , text3 , acc3)
        "naturality>"   ->  poap l >>= \(x , l2) -> poap l2 >>= \(f , _) -> 
                            pure (Naturality x f MSmaller (fald (sortSet r)) , text3 , acc3)
        "if"            ->  poap l >>= \(x , l2) -> poap l2 >>= \(c , l3) -> poap l3 >>= \(d , l4) -> poap l4 >>= \(p , l4) -> 
                            pure (If x c d p (fald (sortSet r)) , text3 , acc3)
        "flip"          ->  pure (Flip (cleanDict (zip l r)) , text3 , acc3)
        "mirror"        ->  pure (Mirror (cleanDict (zip l r)) , text3 , acc3)
        "toggle"        ->  pure (Toggle (cleanDict (zip l r)) , text3 , acc3)
        _               ->  Err ("Non-existent schema called: " ++ schem)

-- =====================
    
parseDisp :: Bool -> Int -> [Sig] -> String -> Error (Int , [Sig] , [Disp])
parseDisp b t sig comment = parseDisp' "" b t "" sig [] comment >>= \(i , sig' , disp) -> Cor (i , sig' , reverse disp)

relatBox :: Relat -> Morph 
relatBox (mr , m , n , name , why) = 
    let (a , _) = typeMorph m in 
    Op (Start a) 0 (Comp (RS mr n name why) m)

relatMem :: Relat -> Mem 
relatMem (mr , m , n , name , why) = (m , 0 , (m , Spra [((n , mr , name , why , relatBox (mr , m , n , name , why)) , Spra [])]) , pure (n , Spra []))

bindX :: String -> Error a -> (a -> Error b) -> Error b
bindX s (Err z) _ = Err (s ++ "\n" ++ z)
bindX _ (Cor a) f = f a

-- first setting declares whether proofs are loaded
parseDisp' :: String -> Bool -> Int -> String -> [Sig] -> [Disp] -> String -> Error (Int , [Sig] , [Disp]) 
parseDisp' acc b c comment sig past text = let (word , text1 , acc1) = parseWord acc text  in case word of 
    "op"        ->  bindX "While parsing operation" (parseOper acc1 text1)
                    (\(o , text2 , acc2) ->      
                    parseDisp' "" b c comment (sig ++ [o]) (Opera o acc2 : past) text2)
    "lem"       ->  parseRelation acc1 Lemma sig text1 >>= \(rel , text2 , acc2) -> 
                    parseDisp' "" b (c+1) "" sig (Displ rel Nop Nothing comment True acc2 : past) text2
    "lem-hide"  ->  parseRelation acc1 Lemma sig text1 >>= \(rel , text2 , acc2) -> 
                    parseDisp' "" b (c+1) comment sig (Displ rel Nop Nothing comment False acc2 : past) text2
    "def"       ->  parseRelation acc1 Axiom sig text1 >>= \(rel , text2 , acc2) -> 
                    parseDisp' "" b (c+1) "" sig (Displ rel Nop Nothing comment True acc2 : past) text2
    "def-hide"  ->  parseRelation acc1 Axiom sig text1 >>= \(rel , text2 , acc2) ->
                    parseDisp' "" b (c+1) comment sig (Assum rel acc2 : past) text2
    "show"      ->  parseShow acc1 sig text1 >>= \(rel , text2 , acc2) -> 
                    parseDisp' "" b (c+1) "" sig (Displ rel Nop Nothing comment True acc2 : past) text2
    "note"      ->  parseName acc1 text1 >>= \(s , text2 , acc2) ->
                    parseDisp' acc2 b c s sig past text2
    "example"   ->  parseRelation acc1 Lemma sig text1 >>= \(rel , text2 , acc2) -> 
                    parseDisp' "" b (c+1) "" sig (Displ rel Nop Nothing comment True acc2 : past) text2
    -- do differently
    "proof"     ->  parsePruf acc1 sig text1 >>= \(p , text2 , acc2) -> 
                    parseDisp' "" b c "" sig (tossProof p acc2 past) text2
                    --if b then fmap (second (Displ (proofRelat p) Nop (Just (proofMem (sprawlProofFromTrace p))) comment True acc2 :)) (parseDisp' "" b c "" sig text2)
                    --     else parseDisp' acc2 b c "" sig text2
    "schema"    ->  parseSchem acc1 sig text1 >>= \(schem , text2 , acc2) ->
                    parseDisp' "" b c "" sig (Schem schem acc2 : past) text2
    ""          ->  pure (c , sig , past)
    s           ->  Err ("Next function: " ++ s ++ " , does not exist/cannot be parsed") --pure (c , sig , past)


tossProof :: Proof -> String -> [Disp] -> [Disp]
tossProof _ _ [] = []
tossProof pruf pruf_code (Displ rel _ mem comment hid rel_code : l) = Displ rel (Yep pruf False pruf_code) mem comment hid rel_code : l
tossProof _ _ (d : l) = d : l

-- IMPORT STRUCTURE
parseDLoc :: Bool -> Int -> [String] -> String -> [Sig] -> FilePath -> IO (Int , [Sig] , [Disp] , Disp , [Disp] , [String])
parseDLoc b c struc file sig fp
    |   inList file struc   =   return (c , sig , [] , Initi (fp ++ file ++ ".txt") "" , [] , struc)
    |   otherwise           =   let filep = (fp ++ file ++ ".txt") in
                                do {
                                putStrLn ("Importing: " ++ filep);
                                doesFileExist filep >>= \exists ->
                                if exists then
                                    readFile filep >>= \s ->
                                    let z = s in -- strip s in 
                                    parseDFile "" b c (file : struc) file sig z fp -- >>= \(c' , sig' , disp1' , disp2' , struc') -> return (c' , sig' , disp1' , disp2' , struc')
                                else do {putStrLn ("--------\n" ++ "Could not load file " ++ filep ++ "\n") ; return (c , [] , [] , Initi "" "" , [] , struc)}
                                }

parseDFile :: String -> Bool -> Int -> [String] ->  String -> [Sig] -> String -> FilePath -> IO (Int , [Sig] , [Disp] , Disp , [Disp] , [String])
parseDFile acc b c struc file sig text fp =    case popChar acc text of
    Just ('i' , _ , _)  ->  
                let (_ , text2 , acc2) = parseWord acc text in 
                let (file' , text3 , acc3) = parseWord acc2 text2 in
                parseDLoc False c struc ("/" ++ file') sig fp >>= \(c' , sig' , disp1' , now' , disp2' , struc') ->
                if nimiti now' then
                    return (c , [] , [] , Initi "" "" , [] , struc)
                else
                    parseDFile acc3 b c' struc' file sig' text3 fp >>= \(c'' , sig'' , disp1'' , now'' , disp2'' , struc'')  ->  
                    return (c'' , sig'' , disp1' ++ now' : disp2' ++ disp1'' , now'' , disp2'' , struc'')
    Just (_ , _ , _)    ->  case parseDisp b c sig text of 
        Cor (c' , sig' , disp')     ->  return (c' , sig' , [] , Initi (fp ++ file ++ ".txt") acc , disp' , struc)  
        Err s                       ->  do {putStrLn ("--------\n" ++ "Error while parsing " ++ fp ++ file ++ ".txt" ++ "\n" ++ s ++ "\n--------") ; return (c , [] , [] , Initi "" "" , [] , struc)}
    Nothing             ->  return (c , [] , [] , Initi (fp ++ "/" ++ file ++ ".txt") acc , [] , struc)


-- Information of current "page" in the loaded document
--          current relation
--                  current theory
--                          next assertions
--                                  previous assertions  
--                                      comment          
--                                                      file
type Page = (Relat, Maybe Mem , Theor,  [Disp], Disp , [Disp] , String , String)

pagePar :: Page -> Par Morph 
pagePar (_ , _ , (_ , _ , _ , par) , _ , _ , _ , _ , _) = par

pageSig :: Page -> [Sig]
pageSig (_ , _ , (sig , _ , _ , _) , _ , _ , _ , _ , _) = sig

pageFile :: Page -> String 
pageFile (_ , _ , _ , _ , _ , _  , _ , file) = file

nimiti :: Disp -> Bool
nimiti (Initi "" "") = True
nimiti _ = False

initPage :: Bool -> String -> FilePath -> IO (Maybe Page) 
initPage b file fp = 
    parseDLoc b 0 [] file [] fp >>= \(_ , _ , disp1 , now , disp2 , _) -> 
    if nimiti now then 
        return Nothing
    else
        theorySteps ([] , [] , [] , []) disp1 now >>= \t -> 
        fmap Just (newSteps' t (now : disp2) (reverse disp1) file)

nextPage :: Page -> IO Page 
nextPage (_ , v ,t , d1 , now , d2 , _ , file) = newSteps t d1 (setMemory v now) d2 file

-- go back through history to the last display, and regenerate state for this
previousPage :: Page -> IO Page 
previousPage (r , v ,t , d1 , now , d2 , comment , file) = 
    let now' = setMemory v now in
    case popDisp (now' : d2) of 
    Nothing                 ->  return (r , v , t , d1 , now' , d2 , comment , file)
    Just (d21 , z , d22)    ->  theorySteps ([] , [] , [] , []) (reverse d22) (Initi "" "") >>= \t' -> 
        newSteps' t' (z : reverse d21 ++ d1) d22 file


-- introducing a duplicate operation removes all prior equations mentioning the previous one.
newStep' :: Theor -> [Disp] -> Disp -> [Disp] -> IO (Theor , [Disp] , Disp , [Disp] , Maybe (Relat , Maybe Mem , String))
newStep' t@(sigs , schem , re , par) futu now past = case dispLemma now of
    Just rel    ->  let relat = sieveRelat (rel : newRelats schem [rel]) in
                    newStep (sigs , schem , filterAdd' relat re , addRelatsPar relat par)  futu (now : past)
    Nothing     ->  newStep t futu (now : past)

newStep :: Theor -> [Disp] -> [Disp] -> IO (Theor , [Disp] , Disp , [Disp] , Maybe (Relat , Maybe Mem , String))
newStep t [] his = return (t , [] , Displ (MEqual , Start 0 , Start 0 , "End" , Axiom) Nop Nothing "" True "" , his , 
                            Just ((MEqual , Start 0 , Start 0 , "End" , Axiom) , Nothing , ""))
newStep theor (Opera s pc : l) his = 
    let Sig c _ _ _ = s in
    let (sigs , schem , rel , par) = flushTheor c theor in
    let relat = sieveRelat (newOp schem (Base s)) in
    do {
        --putStr pc ; 
        return ((sigs ++ [s] , schem  , filterAdd' relat rel , addRelatsPar relat par) , l , Opera s pc , his , Nothing)
    }
newStep (sigs , schem , rel , par) (Schem s pc : l) his = 
    let (s' , schem') = addSchema s schem in
    let relat = sieveRelat (newSchema s' sigs ++ newSchema2 s' rel) in
    do {
        --putStr pc ;
        return ((sigs , schem' , filterAdd' relat rel , addRelatsPar relat par)  , l , Schem s' pc , his , Nothing)
    }
newStep (sigs , schem , rel , par) (Assum s pc : l) his = 
    let relat = sieveRelat (s : newRelats schem [s]) in
    do {
        --putStr pc ;
        return ((sigs , schem , filterAdd' relat rel , addRelatsPar relat par)  , l , Assum s pc , his , Nothing)
    }
newStep (sigs , schem , rel , par) (Displ s puf v c hid pc : l) his 
    |   relatWhy s == Axiom =   let relat = sieveRelat (s : newRelats schem [s]) in
                                do {
                                    --putStr pc ;
                                    return ((sigs , schem , filterAdd' relat rel , addRelatsPar relat par)  , 
                                            l , Displ s puf v c hid pc , his , if hid then Just (s , v , c) else Nothing)
                                }
    |   otherwise           =   do {
                                    --putStr pc ;
                                    return ((sigs , schem , rel , par)  , l , Displ s puf v c hid pc , his , if hid then Just (s , v , c) else Nothing)
                                }
newStep (sigs , schem , rel , par) (Initi fil pc : l) his = 
    do {
        --putStr pc ;
        return ((sigs , schem , rel , par) , l , Initi fil pc , his , Nothing) 
    }

newSteps :: Theor -> [Disp] -> Disp -> [Disp] -> String -> IO Page
newSteps t disp1 now disp2 file = 
    newStep' t disp1 now disp2 >>= \(t' , disp1' , now' , disp2' , x) -> 
    case x of 
        Just (rel , v , comment)    ->  return (rel , v , t' , disp1' , now' , disp2' , comment , file)
        Nothing                     ->  newSteps t' disp1' now' disp2' file

newSteps' :: Theor -> [Disp] -> [Disp] -> String -> IO Page
newSteps' t disp1 disp2 file = 
    newStep t disp1 disp2 >>= \(t' , disp1' , now' , disp2' , x) -> 
    case x of 
        Just (rel , v , comment)    ->  return (rel , v , t' , disp1' , now' , disp2' , comment , file)
        Nothing                     ->  newSteps t' disp1' now' disp2' file

theorySteps :: Theor -> [Disp] -> Disp -> IO Theor 
theorySteps t [] now = newStep' t [] now []  >>= \(t' , _ , _ , _ , _) -> return t'
theorySteps t l now = newStep' t l now [] >>= \(t' , l' , now' , _ , _) -> theorySteps t' l' now'

popDisp :: [Disp] -> Maybe ([Disp] , Disp , [Disp])
popDisp [] = Nothing 
popDisp [_] = Nothing 
popDisp (x : Displ s pruf v c True pc : l) = Just ([x] , Displ s pruf v c True pc , l)
popDisp (x : d : l) = popDisp (d : l) >>= \(d1 , z , d2) -> Just (x : d1 , z , d2)

isEnd :: Relat -> Bool 
isEnd (MEqual , Start 0 , Start 0 , "End" , Axiom) = True 
isEnd _ = False

setMemory :: Maybe Mem -> Disp -> Disp
setMemory (Just viv) (Displ s pruf _ c hid pc) = Displ s pruf (Just viv) c hid pc 
setMemory _ d = d

toss :: a -> [a] -> [a]
toss a [] = [a]
toss a (b : l) = b : a : l

test :: Int -> Int
test a = a * a

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




popChar :: String -> String -> Maybe (Char, String , String)
popChar acc (c : s) 
    |   inList c skip   =   popChar (acc ++ [c]) s
    |   c == '#'        =   let (a , b) = endComment s in
                            popChar (acc ++ '#' : a) b
    |   otherwise       =   Just (c , s , acc ++ [c])
popChar _ _ = Nothing

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
parseName :: String -> String -> Error (String , String , String)
parseName acc =
    parseBrack acc '{' '}'


-- -- SIGNATURE PARSER
-- parseSig :: String -> Maybe (Sig , String)
-- parseSig text =
--     parseBrack '{' '}' text  >>= \(c' , text2)  ->  let (c , _) = nextWord c' in
--     parseBrack '{' '}' text2 >>= \(s  , text3)  ->
--     parseBrack '{' '}' text3 >>= \(i' , text4)  ->  parseNum i' >>= \(i , _) ->
--     parseBrack '{' '}' text4 >>= \(o' , text5)  ->  parseNum o' >>= \(o , _) ->
--         case s of 
--             ('%' : s')  ->  Just (Sig c (Just (linExp 'X' 0) , s') i o , text5)
--             _           ->  Just (Sig c (Nothing , s) i o , text5)

numToParam :: Int -> Param
numToParam i = P (toInteger i % 1)

parseMono :: String -> Error (Mono Param Char)
parseMono [] = pure (0 , [])
parseMono l =   let (a , b) = untilNonnum l in 
                case a of 
                    []  ->  pure (cleanMono (1 , b))
                    _   ->  let (i , _ , _) = parseNum "" a in pure (cleanMono (numToParam i , b))

parsePoly :: String -> Error (Poly Param Char)
parsePoly [] = pure []
parsePoly l = case untilC "" '+' l of 
    Cor (a , b , _) ->  parseMono a >>= \mon -> parsePoly b >>= \pol -> pure (addMono mon pol)
    _               ->  parseMono l >>= \mon -> pure (cleanPoly [mon])

-- EXPRESSION PARSER (TEMPORARY, MUST FIX)
parseExp :: String -> Error (Exp Param) 
parseExp s = parsePoly s >>= \pol -> pure (Pol pol)
-- parseExp [] = Just (constExp 0)
-- parseExp (c : '+' : l) = parseNum l >>= \(i , _) -> Just (linExp c i)
-- parseExp (c : l) = case numParse' c of 
--     Just _      ->  parseNum (c : l) >>= \(i , _) -> Just (constExp i)
--     _           ->  Just (linExp c 0)  


parseOperations' :: [Sig] -> String -> Error [Sig]
parseOperations' _ [] = pure []
parseOperations' sig (' ' : text) = parseOperations' sig text
parseOperations' sig text =
    let (c , _ , _) = nextWord "" text in
    case lookupSig c sig of 
        Nothing     ->  Err ("Reference to non-existent operation: " ++ c)
        Just o      ->
            case untilC "" ',' text of
                Cor (_ , text2 , _)    ->  fmap (o:) (parseOperations' sig text2)
                _                   ->  pure [o]


reconstDisp :: Disp -> String
reconstDisp (Opera _ pc) = pc
reconstDisp (Schem _ pc) = pc
reconstDisp (Assum _ pc) = pc
reconstDisp (Displ _ Nop _ _ _ pc) = pc
reconstDisp (Displ _ (Yep _ _ pc') _ _ _ pc) = pc ++ pc'
reconstDisp (Initi _ pc) = pc
 
reconstPage :: Page -> String -> (String , String)
reconstPage (_ , _ , _ , futu , now , hist , _ , _) = reconstFile (now : hist) futu 

reconstFile :: [Disp] -> [Disp] -> String -> (String , String)
reconstFile hist futu inser = let (a , b) = reconstFileB hist in (a , b ++ inser ++ reconstFileF futu)

reconstFileB :: [Disp] -> (String , String)
reconstFileB [] = ("" , "")
reconstFileB (Initi file pc : _) = (file , pc)
reconstFileB (d : hist) = let (a , b) = reconstFileB hist in (a , b ++ reconstDisp d)

reconstFileF :: [Disp] -> String
reconstFileF [] = ""
reconstFileF (Initi _ _ : _) = ""
reconstFileF (d : futu) = reconstDisp d ++ reconstFileF futu
