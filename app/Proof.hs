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

-- Proof step contains: New state, type or rewrite, name of rewrite, reason why rewrite is allowed, morphism with box of rewrite step
type PrStep = (Morph , MR , String , Why , Morph)

trivPrStep :: PrStep
trivPrStep = (Start 1 , MEqual , "" , Axiom , Start 1)
--  > Begin state
--  > Proof steps:
--      > new morph 
--      > step type 
--      > proof boxed

prStepMorph :: PrStep -> Morph
prStepMorph (m , _ , _ , _ , _) = m

type Proof = (Morph , [PrStep])


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

proofSeq :: Proof -> [Rew]
proofSeq (m , l) = RI m : fmap (\(n , x , name , w , _) -> RS x n name w) l

proofSeqM :: Maybe Proof -> [Rew]
proofSeqM Nothing = []
proofSeqM (Just p) = proofSeq (reverseProof p)

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

lastProof :: Maybe Proof -> (Morph , PrStep)
lastProof (Just (m , [step])) = (m , step)
lastProof (Just (_ , (n , _ , _ , _ , _) : l)) = lastProof (Just (n , l))
lastProof _ = (Start 0 , (Start 0 , MEqual , "" , Axiom , Start 0))

reconstProof :: [Morph] -> Maybe Proof 
reconstProof [] = Nothing 
reconstProof (m : l) = Just (unfoldPreMorph m , fmap reconstStep (m : l))

reconstStep :: Morph -> PrStep
reconstStep box = 
    let n = unfoldPostMorph box in 
    let (mr , name , why) = unfoldInfo box in 
        (n , mr , name , why , box)

proofRelat :: Proof -> Relat 
proofRelat (m , l) = proofRelat' MEqual m m l

proofRelat' :: MR -> Morph -> Morph -> [PrStep] -> Relat 
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
        catPrint m ++ "({" ++ show j ++ "}|" ++ c ++ "|{" ++ show (mo - j - ci) ++ "});"
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
        proofPrint m ++ "({" ++ show j ++ "}|" ++ c ++ "|{" ++ show (mo - j - ci) ++ "});"
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



-- The Sprawl datatype is for storing a tree of all derived morphisms.
-- Each node contains a list of next steps, with information of the proof step stored in PrStep, paired with the Sprawl tree of the next steps.
-- A Sprawl should only contain unique derived morphisms. If there are conflicting derivations, the shortest path is prioritized.
newtype Sprawl =
    Spra [(PrStep , Sprawl)]
    deriving Show

-- A Sprawl-Proof is a Sprawl tree paired with an initial state.
type SprawlProof = (Morph , Sprawl)

-- The main branch of the Sprawl tree will be displayed as a trace of rewrites on the left, and is derived by taking the first element of each list of steps.
-- The following function extracts this main branch
sprawlTrace :: Sprawl -> [PrStep]
sprawlTrace (Spra []) = []
sprawlTrace (Spra ((step , next) : _)) = step : sprawlTrace next

-- Same as above, but will say whether there were alternative steps
sprawlTraceBranch :: Sprawl -> [(PrStep , Bool)]
sprawlTraceBranch (Spra []) = []
sprawlTraceBranch (Spra [(step , next)]) = (step , False) : sprawlTraceBranch next
sprawlTraceBranch (Spra ((step , next) : _)) = (step , True) : sprawlTraceBranch next

sprawlTraceUpto :: Sprawl -> Int -> [PrStep]
sprawlTraceUpto (Spra []) _ = []
sprawlTraceUpto (Spra ((step , next) : _)) i 
    |   i <= 0      =   [] 
    |   otherwise   =   step : sprawlTraceUpto next (i-1)

-- Constructing a sprawl tree from a series of steps
sprawlFromTrace :: [PrStep] -> Sprawl
sprawlFromTrace [] = Spra []
sprawlFromTrace (x : l) = Spra [(x , sprawlFromTrace l)]

sprawlProofTrace :: SprawlProof -> Proof 
sprawlProofTrace (m , p) = (m , sprawlTrace p)

sprawlProofUpto :: SprawlProof -> Int -> Proof
sprawlProofUpto (m , p) i = (m , sprawlTraceUpto p i)

sprawlProofRewBranch :: SprawlProof -> [(Rew , Bool)]
sprawlProofRewBranch (m , s) = (RI m , False) : fmap (\((n , x , name , w , _) , b) -> (RS x n name w , b)) (sprawlTraceBranch s)

sprawlProofFromTrace :: Proof -> SprawlProof 
sprawlProofFromTrace (m , p) = (m , sprawlFromTrace p)

--sprawlPTM :: Maybe SprawlProof -> Proof
--sprawlPTM Nothing = []
--sprawlPTM (Just p) = sprawlProofTrace p

-- Adding new subtree to current branch, at the end
sprawlGraft :: Sprawl -> (PrStep , Sprawl) -> Sprawl
sprawlGraft (Spra l) x = Spra (l ++ [x])

-- Graft at beginning, at index
sprawlGraftI :: Sprawl -> Sprawl -> Int -> Sprawl
sprawlGraftI (Spra []) x _ =    x
sprawlGraftI (Spra (((m , rew , name , why , box) , sub) : l)) (Spra r) i
    |   i <= 0          =   Spra (r ++ ((m , rew , name , why , box) , sub) : l)
    |   otherwise       =   Spra (((m , rew , name , why , box) , sprawlGraftI sub (Spra r) (i-1)) : l)

-- sprawlFind will attempt to find a morphism in a sprawl tree, returning (1) its depth, (2) its subtree, 
-- (3) equivalent sprawltree with the morphism on the main branch, (4) original sprawl tree with morphism and subtree deleted
sprawlFind :: Morph -> Sprawl -> Maybe (Int , Sprawl , Sprawl , Sprawl)
sprawlFind _ (Spra []) = Nothing
sprawlFind m (Spra (((n , rew , name , why , box) , sub) : l))
    |   eqMorph m n         =   Just (1 , sub , Spra (((n , rew , name , why , box) , sub) : l) , Spra l)
    |   otherwise           =   case sprawlFind m sub of 
            Just (i , tree , bran , del)->  Just (i+1 , tree ,  Spra (((n , rew , name , why , box) , bran) : l) , 
                                                                Spra (((n , rew , name , why , box) , del) : l))
            Nothing                     ->  sprawlFind m (Spra l) >>= \(i , tree , bran , del) 
                                        ->  Just (i , tree ,    sprawlGraft bran ((n , rew , name , why , box) , sub) , 
                                                                sprawlGraftI del (Spra [((n , rew , name , why , box) , sub)]) 0)

sprawlProofFind :: Morph -> SprawlProof -> Maybe Int
sprawlProofFind m (n , s)
    |   eqMorph m n     =   Just 0
    |   otherwise       =   sprawlFind m s >>= \(i , _ , _ , _) -> Just (i+1)

-- sprawlIndex: find morphism and subtree at certain index in the main branch of the Sprawl tree
sprawlIndex :: Morph -> Sprawl -> Int -> Maybe (Morph , Sprawl)
sprawlIndex m (Spra []) i
    |   i <= 0      =   Just (m , Spra [])
    |   otherwise   =   Nothing
sprawlIndex m (Spra (((n , mr , name , why , box) , s) : l)) i
    |   i <= 0      =   Just (m , Spra (((n , mr , name , why , box) , s) : l))
    |   otherwise   =   sprawlIndex n s (i-1)


-- sprawlAdd: input is starting morphism, sprawl tree, current index, and new proof step. Adds new step to sprawl-tree. 
-- If new state is in tree, compare distances of proofs and ensure that only the shortest distance is stored.
-- If new state is not in tee, simply add as new branch. Return new sprawl tree with index of new state
sprawlAdd :: Morph -> Sprawl -> Int -> PrStep -> (Sprawl , Int)
sprawlAdd m s i (n , rew , name, why , box) 
    -- Case I: we navigated back to the start. Result: We just return to start then.
    |   eqMorph m n     =   (s , 0)
    |   otherwise       =   case sprawlFind n s of 
    -- Case II: new state cannot be found in the tree. Result: we add new state to tree at current position
        Nothing                     ->  (sprawlGraftI s (Spra [((n , rew , name, why , box) , Spra [])]) i , i+1)
        Just (j , sub , bra , del)  ->  if j < i 
    -- Case III: new state exists in tree, at a better position. Result: do not add new proof step. Instead navigate to this better place
            then (bra , j)
    -- Case IV: new state exists in tree, at worse position. Result: cut out the existing state from tree, with its subtree, and bring to current spot.
            else (sprawlGraftI del (Spra [((n , rew , name, why , box) , sub)]) i  , i+1)

sprawlLength :: Sprawl -> Int 
sprawlLength (Spra []) = 0
sprawlLength (Spra ((_ , sub) : _)) = 1 + sprawlLength sub

sprawlProofLength :: SprawlProof -> Int
sprawlProofLength (_ , s) = 1 + sprawlLength s

sprawlGoal :: SprawlProof -> Morph
sprawlGoal (m , Spra []) = m
sprawlGoal (_ , Spra (((n , _ , _ , _ , _) , sub) : _)) = sprawlGoal (n , sub)

sprawlProofIndex :: SprawlProof -> Int -> Morph
sprawlProofIndex (m , s) i = case sprawlIndex m s i of 
    Just (n , _)    ->  n
    Nothing         ->  m

sprawlNext :: PrStep -> Sprawl -> Int -> PrStep
sprawlNext bs (Spra []) _ = bs
sprawlNext _ (Spra ((st , sub) : _)) i
    |   i <= 0      =   st
    |   otherwise   =   sprawlNext st sub (i-1)

may :: a -> Maybe a -> a
may _ (Just b)  = b
may a Nothing   =   a

sprawlTraceUpTo :: Sprawl -> Int -> [PrStep]
sprawlTraceUpTo (Spra []) _ = []
sprawlTraceUpTo (Spra ((step , next) : _)) i 
    |   i <= 0      =   []
    |   otherwise   =   step : sprawlTraceUpTo next (i-1)

-- Checks if morphism exists in target sprawl, and if so extract final part of trace and add to end
sprawlAddWGoal :: Morph -> Sprawl -> Int -> PrStep -> Maybe SprawlProof -> (Sprawl , Int , Maybe SprawlProof)
sprawlAddWGoal m sprawl i step Nothing = let (x , y) = sprawlAdd m sprawl i step in (x , y , Nothing)
sprawlAddWGoal m sprawl i step (Just (g , gsprawl)) = 
    let (sprawl' , i') = sprawlAdd m sprawl i step in
    let n = prStepMorph step in
    if eqMorph m g then (sprawl' , i' , Just (g , Spra [])) else
    case sprawlFind n gsprawl of 
        Nothing         ->  (sprawl' , i' , Just (g , gsprawl))
        Just (j , _ , gsprawl' , _)          
                        ->  let t = sprawlTraceUpTo gsprawl' j in
                            let (_ , rev) = reverseProof (g , t) in 
                            let revsp = sprawlFromTrace rev in
                            (sprawlGraftI sprawl' revsp i' , i' , Just (g , Spra []))
                            --(sprawl' , i' , Just (Start 10 , Spra []))

lengthSprawlProofM :: Maybe SprawlProof -> Int 
lengthSprawlProofM Nothing = 0 
lengthSprawlProofM (Just p) = sprawlProofLength p

-- toggles an alternative branch of the current proof tree
sprawlToggle :: Sprawl -> Int -> Maybe (Morph , Sprawl)
sprawlToggle (Spra []) _ = Nothing
sprawlToggle (Spra [(x , y)]) i
    |   i <= 1      =   Nothing
    |   otherwise   =   sprawlToggle y (i-1) >>= \(n , s) -> Just (n , Spra [(x , s)])
sprawlToggle (Spra ((x , y) : (x' , y') : l)) i
    |   i <= 0      =   Nothing
    |   i <= 1      =   let (m , _ , _ , _ , _) = x' in Just (m , Spra ((x' , y') : l ++ [(x , y)]))
    |   otherwise   =   sprawlToggle y (i-1) >>= \(n , s) -> Just (n , Spra [(x , s)])

sprawlProofToggle :: SprawlProof -> Int -> Maybe (Morph , SprawlProof)
sprawlProofToggle (m , s) i = sprawlToggle s i >>= \(n , z) -> Just (n , (m , z))

proofCheck :: SprawlProof -> Int -> Maybe SprawlProof -> Bool
proofCheck _ _ Nothing = False
proofCheck (m , p) i (Just (n , _)) = 
    case sprawlIndex m p i of 
        Just (c , _)    -> eqMorph c n
        Nothing         ->  False