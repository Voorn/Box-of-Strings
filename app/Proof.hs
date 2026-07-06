module Proof where

import Morph

-- Whether one relation type supports another
orderMR :: MR -> MR -> Bool
orderMR MEqual _ = True
orderMR MLarger MLarger = True
orderMR MSmaller MSmaller = True
orderMR _ _ = False

-- Whether two relation types are mergeable
compatMR :: MR -> MR -> Bool
compatMR l r = orderMR l r || orderMR r l

-- The merger of two relation types (if mergeable)
mergeMR :: MR -> MR -> MR
mergeMR MEqual r = r
mergeMR l _ = l


--  > Begin state
--  > Proof steps:
--      > new morph 
--      > step type 
--      > proof boxed
type Proof = (Morph , [(Morph , MR , String , Why , Morph)])

reverseBox :: Morph -> Morph 
reverseBox (Start i) = Start i 
reverseBox (Op m i (Base s)) = Op (reverseBox m) i (Base s)
reverseBox (Op m i (Comp (RS x n name w) p)) = Op (reverseBox m) i (Comp (RS (reverseMR x) p name w) n)
reverseBox (Op m i (Comp (RI n) p)) = Op (reverseBox m) i (Comp (RI p) n)
reverseBox (Op m i (Func name n)) = Op (reverseBox m) i (Func name (reverseBox n))


reverseProof :: Proof -> Proof 
reverseProof (m , []) = (m , [])
reverseProof (m , (n , x , name , w , b) : l) = 
    let (m' , l') = reverseProof (n , l) in 
    (m' , l' ++ [(m , reverseMR x , name , w , reverseBox b)])

reverseProofM :: Maybe Proof -> Proof 
reverseProofM Nothing = (Start 0 , [])
reverseProofM (Just p) = reverseProof p

proofM :: Maybe Proof -> Proof 
proofM Nothing = (Start 0 , [])
proofM (Just p) = p

goalProof :: Proof -> Morph 
goalProof (m , []) = m 
goalProof (_ , (m , _ , _ , _ , _) : l) = goalProof (m , l)

proofSeq' :: Proof -> [Rew]
proofSeq' (m , l) = RI m : fmap (\(n , x , name , w , _) -> RS x n name w) l

proofSeq :: Proof -> [Rew]
proofSeq p = reverse (proofSeq' p)

proofSeqM :: Maybe Proof -> [Rew]
proofSeqM Nothing = []
proofSeqM (Just p) = proofSeq p

lengthProof :: Proof -> Int 
lengthProof (_ , l) = 1 + length l

lengthProofM :: Maybe Proof -> Int 
lengthProofM Nothing = 0 
lengthProofM (Just p) = lengthProof p


proofDown :: Int -> Proof -> (Morph , Morph)
proofDown _ (m , []) = (m , m)
proofDown i (_ , (n , _ , _ , _ , box) : lis)
    |   i <= 0      =   (n , box)
    |   otherwise   =   proofDown (i-1) (n , lis)

proofUp :: Int -> Proof -> (Morph , Morph)
proofUp _ (m , []) = (m , m)
proofUp i (m , (n , _ , _ , _ , box) : lis)
    |   i <= 1      =   (m , reverseBox box)
    |   otherwise   =   proofDown (i-1) (n , lis)

popList :: Int -> [a] -> [a]
popList i l = popList' (length l - i) l

popList' :: Int -> [a] -> [a]
popList' _ [] = []
popList' i (a : l)
    |   i <= 0      =   []
    |   otherwise   =   a : popList' (i-1) l

lastProof :: Maybe Proof -> (Morph , Morph , MR , String , Why , Morph)
lastProof (Just (m , [(n , x , name , w , box)])) = (m , n , x , name , w , box)
lastProof (Just (_ , (n , _ , _ , _ , _) : l)) = lastProof (Just (n , l))
lastProof _ = (Start 0 , Start 0 , MEqual , "" , Axiom , Start 0)

reconstProof :: [Morph] -> Maybe Proof 
reconstProof [] = Nothing 
reconstProof (m : l) = Just (unfoldPreMorph m , fmap reconstStep (m : l))

reconstStep :: Morph -> (Morph , MR , String , Why , Morph)
reconstStep box = 
    let n = unfoldPostMorph box in 
    let (mr , name , why) = unfoldInfo box in 
        (n , mr , name , why , box)

proofRelat :: Proof -> Relat 
proofRelat (m , l) = proofRelat' MEqual m m l

proofRelat' :: MR -> Morph -> Morph -> [(Morph , MR , String , Why , Morph)] -> Relat 
proofRelat' mr m n [] = (mr , m , n , "Proof" , Lemma)
proofRelat' mr m _ ((k , kr , _ , _ , _) : l) = proofRelat' (mergeMR mr kr) m k l

proofGoal :: Proof -> Morph 
proofGoal (m , []) = m 
proofGoal (_ , [(n , _ , _ , _ , _)]) = n 
proofGoal (m , _ : l) = proofGoal (m , l)

-- (MR , Morph , Morph , String , Why)

catPrint :: Morph -> String 
catPrint (Start i) = "{" ++ show i ++ "};"
catPrint (Op m j (Base (Sig c _ ci _))) = 
    let (_ , mo) = typeMorph m in 
        catPrint m ++ "({" ++ show j ++ "}|" ++ c : "|{" ++ show (mo - j - ci) ++ "});"
catPrint (Op m j (Comp _ n)) = 
    let (ni , _) = typeMorph n in 
    let (_ , mo) = typeMorph m in 
        catPrint m ++ "({" ++ show j ++ "}|" ++ catPrint n ++ "|{" ++ show (mo - j - ni) ++ "});"
catPrint (Op m j (Func c n)) = 
    let (ni , _) = typeMorph n in 
    let (_ , mo) = typeMorph m in 
        catPrint m ++ "({" ++ show j ++ "}|" ++ c ++ "[" ++ catPrint n ++ "]|{" ++ show (mo - j - ni) ++ "});"


proofPrint :: Morph -> String 
proofPrint (Start _) = ""
proofPrint (Op m j (Base (Sig c _ ci _))) = 
    let (_ , mo) = typeMorph m in 
        proofPrint m ++ "({" ++ show j ++ "}|" ++ c : "|{" ++ show (mo - j - ci) ++ "});"
proofPrint (Op m j (Func c n)) = 
    let (ni , _) = typeMorph n in 
    let (_ , mo) = typeMorph m in 
        catPrint m ++ "({" ++ show j ++ "}|" ++ c ++ "[" ++ proofPrint n ++ "]|{" ++ show (mo - j - ni) ++ "});"
proofPrint (Op m j (Comp (RI _) n)) = 
    let (ni , _) = typeMorph n in 
    let (_ , mo) = typeMorph m in 
        catPrint m ++ "({" ++ show j ++ "}|" ++ proofPrint n ++ "|{" ++ show (mo - j - ni) ++ "});"
proofPrint (Op m j (Comp (RS _ n name _) _)) = 
    let (ni , _) = typeMorph n in 
    let (_ , mo) = typeMorph m in 
        proofPrint m ++ "({" ++ show j ++ "}|[" ++ name ++ "]|{" ++ show (mo - j - ni) ++ "});"
