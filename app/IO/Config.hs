module IO.Config where

import System.Directory



import IO.Parse
import Gloss.Display

loadConfig :: IO [(String , String)]
loadConfig = readFile "config.ini" >>= \s -> return (stringConfig (stripspace s))

stripspace :: String -> String
stripspace (' ' : s) = stripspace s
stripspace ('\t' : s) = stripspace s
stripspace (c : s) = c : stripspace s
stripspace [] = []

stringConfig :: String -> [(String , String)]
stringConfig [] = []
stringConfig (' ' : l) = stringConfig l
stringConfig ('\n' : l) = stringConfig l
stringConfig ('\t' : l) = stringConfig l
stringConfig (c : l) = 
    case untilC "" '=' (c : l) of
        Err _         ->  []
        Cor (a , b , _)    ->  case untilC "" '\n' b of
            Err _     ->  []
            Cor (d , e , _)->  (a , d) : stringConfig e

lookBool :: Bool -> String -> [(String , String)] -> Bool
lookBool b _ [] = b
lookBool b name ((x , y) : l)
    |   name == x   =   if y == "true" then True else (if y == "false" then False else b)
    |   otherwise   =   lookBool b name l

lookInt :: Int -> String -> [(String , String)] -> Int
lookInt b _ [] = b
lookInt b name ((x , y) : l)
    |   name == x   =   let (i , _ , _) = parseNum "" y in i
    |   otherwise   =   lookInt b name l

lookString :: String -> String -> [(String , String)] -> String
lookString b _ [] = b
lookString b name ((x , y) : l)
    |   name == x   =   y
    |   otherwise   =   lookString b name l

lookOrient :: Orient -> String -> [(String , String)] -> Orient
lookOrient b _ [] = b
lookOrient b name ((x , y) : l)
    |   name == x && y == "LR"  =   LR
    |   name == x && y == "RL"  =   RL
    |   name == x && y == "UD"  =   UD
    |   name == x && y == "DU"  =   DU
    |   otherwise               =   lookOrient b name l

settingConfig :: (String , Bool , Bool , Orient , Bool , Bool) -> IO (String , Bool , Bool , Orient , Bool , Bool)
settingConfig (a , b , c , d , e , f) = 
    doesFileExist "config.ini" >>= \v -> 
    if v then
        loadConfig >>= \con -> return (
            lookString a "input" con , 
            lookBool b "darkmode" con , 
            lookBool c "fullscreen" con , 
            lookOrient d "orient" con , 
            lookBool e "zoom" con , 
            lookBool f "sound" con)
    else
        return (a , b , c , d , e , f)




--stringsplit :: String -> Char 
