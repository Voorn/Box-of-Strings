{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Replace case with fromMaybe" #-}
module Parse where

-- standard libraries
import Data.Bifunctor

-- in project libraries
import Morph
import Rewrite
import Theory 
import Par 

-- ===============================================
-- Parsing text from a file to extract information
-- ===============================================

firstelem :: a -> [a] -> a
firstelem a [] = a
firstelem _ (b : _) = b

popelem :: a -> [a] -> (a , [a])
popelem a [] = (a , [])
popelem _ (b : c) = (b , c)

inList :: Eq a => a -> [a] -> Bool
inList _ [] = False 
inList c (d : s) = c == d || inList c s

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
stripNewline ('\n' : s) = stripNewline s
stripNewline ('\r' : s) = stripNewline s
stripNewline ('\t' : s) = stripNewline s
stripNewline (' ' : s) = stripNewline s
stripNewline (c : s) = c : stripNewline s

-- Basic text processing utility
untilC :: Char -> String -> Maybe (String , String)
untilC _ [] = Nothing
untilC c (d : s)
    |   c == d      =   Just ([] , s)
    |   otherwise   =   untilC c s >>= \(x , y) -> Just (d : x , y)

nextC :: String -> (Char , String)
nextC [] = ('x' , [])
nextC (' ' : l) = nextC l
nextC (c : l) = (c , l) 

popChar :: String -> Maybe (Char, String)
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
parseNum' x (c : s)     =   Just (x , c : s)

-- CHARACTER PARSER 
parseChar :: String -> Maybe (Char , String)
parseChar (c : s) = Just (c , s)
parseChar _ = Nothing


-- SIGNATURE PARSER
parseSig :: String -> Maybe (Sig , String)
parseSig text = 
    parseBrack '{' '}' text  >>= \(c' , text2)  ->  parseChar c' >>= \(c , _) ->
    parseBrack '{' '}' text2 >>= \(s  , text3)  -> 
    parseBrack '{' '}' text3 >>= \(i' , text4)  ->  parseNum i' >>= \(i , _) ->
    parseBrack '{' '}' text4 >>= \(o' , text5)  ->  parseNum o' >>= \(o , _) ->
        Just (Sig c s i o , text5)

-- MORPHISM PARSER
parseMorphism :: [Sig] -> Int -> String -> Maybe (Morph , String)
parseMorphism sig i = parseMorphism' sig (Start i)

parseMorphism' :: [Sig] -> Morph -> String -> Maybe (Morph , String)
parseMorphism' sig base text = 
    case untilC ';' text of 
        Nothing             ->  Just (base , text)
        Just (now , nex)    ->  untilC '.' now  >>= \(i' , c')  -> 
                                parseNum i'     >>= \(i  , _ )  -> 
                                parseChar c'    >>= \(c  , _ )  ->
                                lookupSig c sig >>= \o          -> 
                                parseMorphism' sig (Op base i (Base o)) nex

-- OPERATION LIST PARSER 
parseOperations :: [Sig] -> String -> Maybe [Sig]
parseOperations _ [] = Just [] 
parseOperations sig (c : text) = 
    lookupSig c sig >>= \o ->
    case untilC '.' text of 
        Just (_ , text2)    ->  fmap (o:) (parseOperations sig text2)
        _                   ->  Just [o]

-- RELATION PARSER 
parseRelat :: [Sig] -> String -> Maybe (Relat , String)
parseRelat sig text =
    parseBrack '{' '}' text  >>= \(i' , text2)  ->  parseNum i'             >>= \(i , _) ->
    parseBrack '{' '}' text2 >>= \(m' , text3)  ->  parseMorphism sig i m'  >>= \(m , _) ->
    parseBrack '{' '}' text3 >>= \(n' , text4)  ->  parseMorphism sig i n'  >>= \(n , _) ->
        case text3 of 
            ('<' : _)   ->  Just ((MLarger , m , n) , text4)
            ('>' : _)   ->  Just ((MSmaller , m  , n) , text4)
            _           ->  Just ((MEqual , m , n) , text4)

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
        _               ->  Nothing

type Phase = ([Sig] , [Schema] , [Relat] , Relat , String)

-- TEXT PARSER
--                                      New operations, new equations, start, goal, name
parseText :: [Sig] -> [Schema] -> String -> Maybe (Phase , String)
parseText sig hem = parseText' sig hem [] [] []

parseText' :: [Sig] -> [Schema] -> [Sig] -> [Schema] -> [Relat] -> String -> Maybe (Phase , String)
parseText' sig hem newsig newhem neweq text = case popChar text of 
    -- Operation
    Just ('O' , text2)  ->  parseSig text2 >>= \(s , text3) -> 
                            parseText' (sig ++ [s]) hem (newsig ++ [s]) newhem (newOp hem s ++ neweq) text3
    -- ! Displayed Definition 
    Just ('D' , text2)  ->  parseRelat sig text2 >>= \(rel , text3) -> 
                            Just ((newsig , newhem ,rel : neweq , rel , "Definition") , text3)
    -- Assumption, not displayed
    Just ('A' , text2)  ->  parseRelat sig text2 >>= \(rel , text3) -> 
                            parseText' sig hem newsig newhem (rel : neweq) text3
    -- Lemma 
    Just ('L' , text2)  ->  parseRelat sig text2 >>= \(rel , _) -> 
                            Just ((newsig , newhem , neweq , rel , "Lemma") , 'A' : text2)
    -- ! Example
    Just ('E' , text2)  ->  parseRelat sig text2 >>= \(rel , text3) -> 
                            Just ((newsig , newhem , neweq , rel , "Example") , text3)
    -- Schema (adds relevant schema relations)
    Just ('S' , text2)  ->  parseSchema sig text2 >>= \(t , text3) -> 
                            parseText' sig (addSchema t hem) newsig (addSchema t newhem) (newSchema t sig ++ neweq) text3
    -- Basic relation (adds relevant schema relations)
    Just ('B' , text2)  ->  parseBasic sig text2 >>= \(t , text3) -> 
                            parseText' sig hem newsig newhem (newBasic t ++ neweq) text3
    _                   ->  Just ((newsig , newhem , neweq , (MEqual , Start 0 , Start 0) , "End of file") , [])


-- FULL PARSER 
parseAll :: [Sig] -> [Schema] -> String -> [Phase]
parseAll _ _ [] = []
parseAll sig hem text = case parseText sig hem text of 
    Just ((sig' , hem' , equ' , rel , n) , text2)   ->  (sig' , hem' , equ' , rel , n) : parseAll (sig ++ sig') (addSchemas hem' hem) text2
    Nothing                                         ->  []


-- USING DATA
firstPhase :: [Phase] -> Maybe (Relat , String , [Sig] , [Schema] , Par Morph , [Phase])
firstPhase = nextPhase [] [] []

nextPhase :: [Sig] -> [Schema] -> Par Morph -> [Phase] -> Maybe (Relat , String , [Sig] , [Schema] , Par Morph , [Phase])
nextPhase _ _ _ [] = Nothing 
nextPhase sig hem equ ((nsig , nhem , relats , rel , name) : phase)  =   
    Just (rel , name , sig ++ nsig , addSchemas nhem hem , cleanPar (addrelClass relats equ) , phase)

pushPhase :: [Sig] -> [Schema] -> [Relat] -> [Phase] -> [Phase]
pushPhase _ _ _ [] = []
pushPhase sig hem equ ((sig' , hem' , equ' , rel , name) : phase) = (sig ++ sig' , addSchemas hem' hem , equ' ++ equ , rel , name) : phase

 -- EXTRACT THEORY ONLY
theoryPhase :: [Sig] -> [Schema] -> [Relat] -> [Phase] -> ([Sig] , [Schema] , [Relat])
theoryPhase sig hem equ [] = (sig , hem , equ)
theoryPhase sig hem equ ((sig' , hem' , relat , _ , _) : phase) = theoryPhase (sig ++ sig') (addSchemas hem' hem) (relat ++ equ) phase

-- IMPORT STRUCTURE
parseLoc :: [String] -> String -> [Sig] -> [Schema] -> [Relat] -> IO [Phase]
parseLoc struc file sig hem equ 
    |   inList file struc   =   return [] 
    |   otherwise           =   readFile ("input/" ++ file ++ ".txt") >>= \s -> 
                                let z = strip s in parseFile (file : struc) z sig hem equ

parseFile :: [String] -> String -> [Sig] -> [Schema] -> [Relat] -> IO [Phase]
parseFile struc text sig hem equ =    case popChar text of 
    Just ('I' , text2)  ->  case parseBrack '{' '}' text2 of 
        Just (file , text3) ->  parseLoc struc file sig hem equ >>= \phase -> 
                                let (sig' , hem' , equ') = theoryPhase sig hem equ phase in
                                parseFile struc text3 sig' hem' equ'
        _                   ->  return []
    Just (c , text2)    ->  let phase = parseAll sig hem (c : text2) in 
                            let phase' = pushPhase sig hem equ phase in 
                                return phase'
    Nothing             ->  return []



