module Write where

import Morph
import Gloss.World
import Parse
import Proof
import System.Directory (doesFileExist)


morphSaveX :: Int -> Morph -> String
morphSaveX _ (Start _) = "id"
morphSaveX j (Op m i (Base (Sig c (Nothing , _) _ _))) = morphSaveX' j m ++ show (i+j) ++ ":" ++ [c]
morphSaveX j (Op m i (Base (Sig c (Just ex , _) _ _))) = morphSaveX' j m ++ show (i+j) ++ ":" ++ c : '(' : show ex ++ ")"
morphSaveX j (Op m i (Comp (RS mr k name _) n)) = let (a , _) = typeMorph n in
    morphSaveX' j m ++ show (i+j) ++ ":[" ++ name ++ " (" ++ show a ++ ") {" ++ morphSaveX 0 n ++ ' ' : mrSave mr : ' ' : morphSaveX 0 k ++ "}]"
morphSaveX j (Op m i (Comp _ n)) = morphSaveX' j m ++ morphSaveX (i+j) n
morphSaveX j (Op m i (Func _ n)) = morphSaveX' j m ++ morphSaveX (i+j) n

morphSaveX' :: Int -> Morph -> String
morphSaveX' _ (Start _) = ""
morphSaveX' j m = morphSaveX j m ++ ", "

morphSave :: Int -> Morph -> String
morphSave _ (Start _) = ""
morphSave j (Op m i (Base (Sig c _ _ _))) = morphSave j m ++ "\n\t" ++ show (i+j) ++ "." ++ c : ";"
morphSave j (Op m i (Comp _ n)) = morphSave j m ++ morphSave (i+j) n
morphSave j (Op m i (Func _ n)) = morphSave j m ++ morphSave (i+j) n


morphSaveNLS :: Int -> Morph -> String
morphSaveNLS _ (Start _) = ""
morphSaveNLS j (Op m i (Base (Sig c _ _ _))) = morphSaveNLS j m ++ show (i+j) ++ "." ++ c : ";"
morphSaveNLS j (Op m i (Comp _ n)) = morphSaveNLS j m ++ morphSaveNLS (i+j) n
morphSaveNLS j (Op m i (Func _ n)) = morphSaveNLS j m ++ morphSaveNLS (i+j) n

mrSave :: MR -> Char
mrSave MEqual = '='
mrSave MLarger = '<'
mrSave MSmaller = '>'


morphBoxSave :: Int -> Morph -> String
morphBoxSave _ (Start _) = ""
morphBoxSave j (Op m i (Base (Sig c _ _ _))) = morphBoxSave j m ++ show (i+j) ++ "." ++ c : ";"
morphBoxSave j (Op m i (Comp (RS mr k nam _) n)) =
    let (a , _) = typeMorph n in
    morphBoxSave j m ++ show (i+j) ++ ".{" ++ show a ++ "}{" ++ nam ++ "}{" ++ morphSaveNLS 0 n ++ "}" ++ mrSave mr : '{' : morphSaveNLS 0 k ++ "};"
morphBoxSave j (Op m i (Comp (RI k) n)) =
    let (a , _) = typeMorph n in
    morphBoxSave j m ++ show (i+j) ++ ".{" ++ show a ++ "}{}{" ++ morphSaveNLS 0 n ++ "}={" ++ morphSaveNLS 0 k ++ "};"
morphBoxSave _ _ = ""


writeFileAdd :: String -> String -> IO ()
writeFileAdd file_name new_line =
    doesFileExist file_name >>= \b ->
    if b then
        readFile file_name >>= \content ->
        let content2 = content ++ "\n" ++ new_line in
        do {putStrLn content2 ;
            writeFile file_name content2}
    else
        writeFile file_name new_line


writeOperation :: String -> Sig -> IO ()
writeOperation file_name (Sig c (_ , "") a b) =
    let line = "\nop  " ++ c : " : " ++ show a ++ " -> " ++ show b in
    writeFileAdd ("input/" ++ file_name ++ ".txt") line
writeOperation file_name (Sig c (_ , style) a b) =
    let line = "\nop  " ++ c : " : " ++ show a ++ " -> " ++ show b ++ " [" ++ style ++ "]" in
    writeFileAdd ("input/" ++ file_name ++ ".txt") line
--writeOperation file_name (Sig c (_ , style) a b) =
--    let line = "Operation{" ++ c : "}{" ++ style ++ "}{" ++ show a ++ "}{" ++ show b ++ "}" in
--    writeFileAdd ("input/" ++ file_name ++ ".txt") line

writePlay :: String -> Morph -> IO ()
writePlay file_name m =
    let (a , _) = typeMorph m in
    let mtext = morphSave 0 m in
    let line = "Play{" ++ show a ++ "}{" ++ mtext ++ "}" in
        writeFileAdd ("input/" ++ file_name ++ ".txt") line

writeLemma :: Wtyp -> String -> Morph -> Morph -> IO ()
writeLemma wtyp file_name m n =
    let (a , _) = typeMorph m in
    let mtext = morphSaveX 0 m in
    let ntext = morphSaveX 0 n in
    let styp = if wtyp == WDef then "\ndef  Unnamed (" else "\nlem  Unnamed (" in
    let line = styp ++ show a ++ ") {\n    " ++ mtext ++ "\n    =\n    " ++ ntext ++ "\n}" in
        writeFileAdd ("input/" ++ file_name ++ ".txt") line
-- writeLemma wtyp file_name m n =
--     let (a , _) = typeMorph m in
--     let mtext = morphSave 0 m in
--     let ntext = morphSave 0 n in
--     let styp = if wtyp == WDef then "Definition" else "Lemma" in
--     let line = styp ++ "{" ++ show a ++ "}{" ++ mtext ++ "\n}{" ++ ntext ++ "\n}" in
--         writeFileAdd ("input/" ++ file_name ++ ".txt") line



tol :: [a] -> [a]
tol [] = []
tol (_ : l) = l

-- set lemma
setRelatWorld :: Wtyp -> Relat -> World -> World
setRelatWorld wty relat w =
    let (currel , mem , theor , disp1 , disp2 , comment , file) = document w in
    let disp1' = if wty == WDef then Assum relat : Displ relat Nothing "" : disp1
                                else Displ relat Nothing "" : Assum relat : disp1  in
    let page = nextPage (currel , mem , theor , disp1' , tol disp2 , comment , file) in
        pageWorld (worldSize w) (worldOrient w) page (worldExtra w)

setOperWorld :: Sig -> World -> World
setOperWorld op w =
    let (currel , mem , theor , disp1 , disp2 , comment , file) = document w in
    let disp1' = Opera op : disp1 in
    let page = nextPage (currel , mem , theor , disp1' , tol disp2 , comment , file) in
        pageWorld (worldSize w) (worldOrient w) page (worldExtra w)


-- ===================================
-- Proofs 
-- ===================================
saveMR :: MR -> String
saveMR MEqual = "="
saveMR MLarger = "<"
saveMR MSmaller = ">"


breakString :: String -> [String]
breakString l = let (s , r) = breakString' l in s : r

breakString' :: String -> (String , [String])
breakString' [] = ("" , [])
breakString' ('\n' : l) = let r = breakString l in ("" , r)
breakString' ('\t' : l) = let (s , r) = breakString' l in ("   " ++ s , r)
breakString' (c : l) = let (s , r) = breakString' l in (c : s , r)

-- saveMorphLines' :: String -> Morph -> String
-- saveMorphLines' ind (Start a) = "{" ++ show a ++ "}{"
-- saveMorphLines' ind (Op m i (Base (Sig c _ _ _))) = saveProofStep m ++ show i ++ '.' : c : ";"
-- saveMorphLines' ind (Op m i (Comp (RS x no _ _) ni)) =
--     let (a , _) = typeMorph no in
--     saveProofStep m ++
--     show i ++ "." ++ saveMR x ++ "{" ++ show a ++ "}{" ++ morphSaveNLS 0 ni ++ "}{" ++ morphSaveNLS 0 no ++ "};"
-- saveMorphLines' ind (Op m _ (Comp (RI no) ni)) =
--     let (a , _) = typeMorph no in
--     saveProofStep m ++
--     "={" ++ show a ++ "}{" ++ morphSaveNLS 0 ni ++ "}{" ++ morphSaveNLS 0 no ++ "};"
-- saveMorphLines' ind (Op m _ (Func {})) =
--     saveProofStep m


proofSave :: Proof -> String
proofSave (_ , []) = ""
proofSave (_ , [(_ , _ , _ , _ , box)]) = "\t" ++ morphSaveX 0 box ++ "\n"
proofSave (_ , (n , _ , _ , _ , box) : l) = "\t" ++ morphSaveX 0 box ++ "\n\t=\n" ++ proofSave (n , l)

saveProof :: Proof -> String
saveProof (_ , []) = ""
saveProof (_ , [_]) = ""
saveProof (m , l) =
    let (a , _) = typeMorph m in
    ("proof  (" ++ show a ++ ") {\n" ++ proofSave (m , l) ++ "}\n")

writeProof :: Proof -> String -> IO ()
writeProof p file =
    writeFileAdd ("output/" ++ file ++ ".txt") (saveProof p)

saveWhy :: Why -> String 
saveWhy Axiom = "def"
saveWhy Lemma = "lem"
saveWhy _ = "?"

saveRelat :: Relat -> String
saveRelat (mr , m , n , name , why) 
    |   m == n      =   let (a , _) = typeMorph m in 
                        "\nshow  " ++ name ++ " (" ++ show a ++ ") {\n\t" ++ morphSaveX 0 m ++ "\n}\n"
    |   otherwise   =   let (a , _) = typeMorph m in 
                        "\n" ++ saveWhy why ++ "  " ++ name ++ " (" ++ show a ++ ") {\n\t" ++ morphSaveX 0 m ++ "\n\t" ++ saveMR mr ++ "\n\t" ++ morphSaveX 0 n ++ "\n}\n"