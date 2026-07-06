module HyperMatch where

import Morph
import Par
import Par2

morphOnly :: (Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)]))
    -> Morph -> Maybe Morph
morphOnly f m = f m ([(0 , 0, False) | _ <- [0..lengthMorph m]]) >>= \(n , _) -> Just n

trySwap :: Int -> Bool -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
trySwap i k (Op (Op m a op) b qp) (x : y : l)
    |   i <= 0 && k     =   let (opi , opo) =   typeOper op in
                            let (qpi , qpo) =   typeOper qp in
                            if (b + qpi) <= a then Just (Op (Op m b qp) (a-qpi+qpo) op , y : x : l) else
                            if (a + opo) <= b then Just (Op (Op m (b-opo+opi) qp) a op , y : x : l) else
                            Nothing
    |   i <= 0          =   let (opi , opo) =   typeOper op in
                            let (qpi , qpo) =   typeOper qp in
                            if (a + opo) <= b then Just (Op (Op m (b-opo+opi) qp) a op , y : x : l) else
                            if (b + qpi) <= a then Just (Op (Op m b qp) (a-qpi+qpo) op , y : x : l) else
                            Nothing
    |   otherwise       =   trySwap (i-1) k (Op m a op) (y : l) >>= \(m' , l') -> Just (Op m' b qp , x : l')
trySwap _ _ _ _           =   Nothing

-- Joinkers attempt to remove any operations in between two marked operations
tryJoinkerL :: Int -> Int -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
tryJoinkerL i j m loc
    |   j <= i      =   Just (m , loc)
    |   otherwise   =   trySwap (j-1) True m loc >>=
                        \(n , voc) -> tryJoinkerL i (j-1) n voc

tryJoinkerLany :: Int -> Int -> Int -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
tryJoinkerLany i k j m loc
    |   k < j       =    case tryJoinkerL i k m loc of
                            Just v      ->   Just v
                            Nothing     ->  tryJoinkerLany i (k+1) j m loc
    |   otherwise   =   Nothing

tryJoinkerR :: Int -> Int -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
tryJoinkerR i j m loc
    |   j >= i      =   Just (m , loc)
    |   otherwise   =   trySwap j True m loc >>= \(n , voc) -> tryJoinkerR i (j+1) n voc

tryJoinkerRany :: Int -> Int -> Int -> Morph -> [(Float , Float , Bool)] -> Maybe (Morph , [(Float , Float , Bool)])
tryJoinkerRany i k j m loc
    |   k > j       =   case tryJoinkerR i k m loc of
                            Just v      ->   Just v
                            Nothing     ->  tryJoinkerRany i (k-1) j m loc
    |   otherwise   =   Nothing

-- ===================================

cutMorph :: Morph -> Int -> Morph
cutMorph (Start a) _ = Start a
cutMorph (Op m a op) i
    |   i <= 0      =   let (_ , out) = typeMorph m in Op (Start out) a op
    |   otherwise   =   Op (cutMorph m (i-1)) a op

-- removing wires above and below morphism
trimMorph :: Morph -> Int -> Int -> Morph
trimMorph (Start a) i j = Start (a - i - j)
trimMorph (Op m a op) i j = Op (trimMorph m i j) (a - i) op

-- how many wires above and below morphism
flufMorph :: Morph -> (Int , Int , Int)
-- un-used case
flufMorph (Start a) = (0 , a , 0)
flufMorph (Op (Start a) b op) = let (inp , out) = typeOper op in (b , out , a - b - inp)
flufMorph (Op m b op) =
    let (x , y , z) = flufMorph m in
    let t = x + y + z in
    let (inp , out) = typeOper op in
    let (x' , z') = (min x b , min z (t - b - inp)) in
        (x' , t - x' - z' - inp + out , z')

cropMorph :: Morph -> Morph
cropMorph m = let (x , _ , z) = flufMorph m in trimMorph m x z

-- checking if match found up to now is correct
quickCheck :: Morph -> Int -> Morph -> Int -> Bool
quickCheck _ _ (Start _) _ = False
quickCheck m i (Op p _ (Comp _ n)) v
    |   v <= 0          =   eqMorph n (cropMorph (cutMorph m i))
    |   otherwise       =   quickCheck m i p (v-1)
quickCheck m i (Op n _ _) v
    |   v <= 0          =   False
    |   otherwise       =   quickCheck m i n (v-1)

-- hypermatch
popMorph :: Morph -> Int -> Morph
popMorph (Start a) _ = Start a
popMorph (Op m a op) i
    |   i <= 0      =   Op m a op
    |   otherwise   =   popMorph m (i-1)

findOper :: Morph -> Oper -> Int -> Int -> [Int]
findOper (Start _) _ _ _ = []
findOper (Op m _ op) qp i j
    |   i < j       =   findOper m qp (i+1) j
    |   op == qp    =   i : findOper m qp (i+1) j
    |   otherwise   =   findOper m qp (i+1) j

nextOp :: Morph -> Int -> Maybe Oper
nextOp (Start _) _  =   Nothing
nextOp (Op m _ op) i
    |   i <= 0      =   Just op
    |   otherwise   =   nextOp m (i-1)

boxitup :: Morph -> Int -> Morph
boxitup (Start a) _ =   Start a
boxitup (Op m a op) i
    |   i <= 0      =   let bop = operMorph op in
                        Op m a (Comp (RI bop) bop)
    |   otherwise   =   Op (boxitup m (i-1)) a op

-- ======================


-- Attempt to pull as many operation between -k- and -i- right of -i-
hypmaPullRany :: Morph -> Int -> Int -> Int -> (Morph , Int)
hypmaPullRany m k i j
    |   j >= k      =   case morphOnly (tryJoinkerR i j) m of
            Just n  ->  hypmaPullRany n k (i-1) (j-1)
            Nothing ->  hypmaPullRany m k i (j-1)
    |   otherwise   =   (m , i)

-- Attempt to pull as all operation between -k- and -i- to left of -k-
hypmaPullLall :: Morph -> Int -> Int -> Maybe Morph
hypmaPullLall m k i
    |   (k+1) < i   =   morphOnly (trySwap k True) m >>= \n -> hypmaPullLall n (k+1) i
    |   otherwise   =   Just m

-- match a morphism inside a bigger morphism
hypmaInit :: Morph -> Morph -> Maybe (Morph , Int)
hypmaInit (Start _) _ = Nothing
hypmaInit (Op m a op) n =
    let lis = findOper n op 0 0 in
        tryAny (hypmaInit2 (Op m a op) n) lis

hypmaInit2 :: Morph -> Morph -> Int -> Maybe (Morph , Int)
hypmaInit2 m n i = --Just (boxitup n i)
    let (n' , i') = hypmaPullRany (boxitup n i) 0 i (i-1) in
    hypmaBlock m 1 n' i'


-- match -m- in -n- just after operation at index -i-
-- Property (I) which is to be maintained: "match is as far to the left as possible"
hypmaBlock :: Morph -> Int -> Morph -> Int -> Maybe (Morph , Int)
hypmaBlock m k n i =
    case nextOp m k of
        Just op     ->  let lis = findOper n op 0 (i+1) in
                        tryAny (hypmaBlock2 m k n i) lis
        Nothing     ->  Just (n , i)

-- match -m- in -n-. Currently checking for potential -k-th- element of -m-, looking at candidate -j- in -n-. 
-- Existing partial match is at -i-, so we need to see if -j- can be brought next to -i- and whether that creates a partial match 
hypmaBlock2 :: Morph -> Int -> Morph -> Int -> Int -> Maybe (Morph , Int)
hypmaBlock2 m k n i j =
    -- Step 1: try to move as much between -i- and -j- to the right of -j- (to maintain propert (I))
    let (n1 , j1) = hypmaPullRany n (i+1) j (j-1) in
    -- Step 2: try to move all remaining operations between -i- and -j- left of -i-, fail if impossible
    hypmaPullLall n1 i j1 >>= \n2 -> let i2 = j1-1 in
    -- Step 3: Merge new operation into existing match
    mergeIndex n2 i2 >>= \n3 ->
    -- Step 4: Check if new merge forms partial match
    if quickCheck m k n3 i2 then
    -- Step 5: Recursively call to continue matching
    hypmaBlock m (k+1) n3 i2
    else Nothing

hypmaRewrite :: Morph -> Morph -> Int -> Morph
hypmaRewrite _ (Start a) _ = Start a
hypmaRewrite m (Op n a op) i
    |   i <= 0      =   let (_ , nout) = typeMorph n in
                        let (minp , _) = typeMorph m in
                        let b = nout - a - minp in
                        let m' = weakenMorph a b m in
                            compMorph m' n
    |   otherwise   =   Op (hypmaRewrite m n (i-1)) a op

hypmaBox :: Morph -> Morph -> Morph -> Int -> MR -> String -> Why -> Morph
hypmaBox _ _ (Start a) _ _ _ _ = Start a
hypmaBox x y (Op n a op) i mr name why
    |   i <= 0      =   Op n a (Comp (RS mr y name why) x)
    |   otherwise   =   Op (hypmaBox x y n (i-1) mr name why) a op

flatterMorph :: Morph -> Morph
flatterMorph (Start a) = Start a
flatterMorph (Op m a (Comp _ (Op (Start _) _ qp))) = Op (flatterMorph m) a qp
flatterMorph (Op m a op) = Op (flatterMorph m) a op

testMatch :: Morph -> Morph
testMatch m = maybe m fst (hypmaInit (Start 1) m)

testRewrite :: (Morph , Morph) -> Morph -> Morph
testRewrite (a , b) m =
    case hypmaInit a m of
        Just (m' , i)   ->  hypmaRewrite b m' i
        Nothing         ->  m


hypmaRewriteAll :: [(Morph , Morph)] -> Morph -> Par Morph ->  Maybe (Morph , MR , String , Why , Morph)
hypmaRewriteAll [] _ _ = Nothing
hypmaRewriteAll ((a , b) : l) m qop =
    case hypmaInit a m of
        Just (m' , i)   ->  let (mr , name , why) = findName qop a b in Just (flatterMorph (hypmaRewrite b m' i) , mr , name , why , hypmaBox a b m' i mr name why)
        Nothing         ->  hypmaRewriteAll l m qop


