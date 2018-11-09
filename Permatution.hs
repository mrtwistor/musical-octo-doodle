{-# LANGUAGE TypeSynonymInstances #-}
module Permatution where
import qualified Data.List   as L
import           Data.Map
import qualified Data.Tree   as T
import           Debug.Trace (trace)

type Permatution = Map Int [Int]

intercalate :: Permatution -> Permatution -> Permatution
intercalate = unionWith (++)


ofCycle :: [Int] -> Permatution
ofCycle l
  = L.foldl
    (\ac (xn,xn1) ->
       insertWith (++) xn [xn1] ac)
    empty
    (
      let (t,[h]) = L.splitAt (-1+length l) l
      in zip l (h:t)
    )


ofCycles :: [[Int]] -> Permatution
ofCycles = L.foldl (\ac x -> unionWith (++) ac (ofCycle x)) empty

m1 = ofCycle [1,1,2,2,3,4,5,2,3,4]
m2 = ofCycle [4,5,2,1,3,2,1,3,3,4]
m3 = ofCycle [2,3,4,5,1,2,3,4,5,1]


apply p a =
  let consume k (h:t) =
        Just t
      consume k [] =
        Nothing
  in let elem = head ( p ! a )
  in (elem, updateWithKey consume a p)

-- Apply permatution p to list of values
applyList p = reverse . fst . L.foldl (\(ac, p') x-> let (x', p'') = apply p' x in (x' : ac, p'')) ([],p)

-- Ex: applyList m1 [1,1,2,2,2,3,3,4,4,5]

cycleFrom :: Permatution -> Int -> Int -> (Permatution,[Int])
cycleFrom p x y =
  let (x', p') = apply p x
  in
    if x' == y then (p',[x])
    else let (p'', c) = cycleFrom p' x' y
         in (p'', c ++ [x])


toCycles p =
  case minViewWithKey p of
    Just ((k,(_:_)), _) ->
      let (p', c) = cycleFrom p k k
      in c : toCycles p'
    Just ((k,[]), p') -> toCycles p'
    Nothing -> []

--Examples
perm1 :: Permatution
perm1 = fromList [(1,[1,2]),(2,[2,1]),(3,[3])]
perm2 :: Permatution
perm2 = fromList [(1,[1,2]),(2,[2,1]),(3,[3])]
ex1=toCycles $ (ofCycle [1,2,3,4]) `intercalate` (ofCycle[5,6,7])





insertL :: a -> Int -> [a] -> [a]
insertL x 0 l       = x : l
insertL x n (h : t) = h : insertL x (n-1) t

--Permutations as a comprehension:
permutations [] = [[]]
permutations (h : t) = [ insertL h k s | k <- [0..(length t)], s <- permutations t]
--Permutations with signature:
permutationsWithSgn [] = [(1,[])]
permutationsWithSgn (h : t) = [ (sgn*(-1)^k, insertL h k s) | k <- [0..(length t)], (sgn,s) <- permutationsWithSgn t]


--Deletes a single element from a list in all possible ways, returning a pair (x,rest) where
--x is the deleted element and rest is the rest of the list
deleteOne []      = []
deleteOne (h : t) = (h,t) : ((\(h1,t1)->(h1,h:t1)) <$> deleteOne t)

--Permutation tree
permutationsT l =
  T.Node [] $
  (\(h,t)->
      (permutationsT t) >>= (\x-> T.Node (h:x) [])
  )
  <$> deleteOne l

--Tikz code for Tree drawing:
drawTikz :: Show a=>(T.Tree a) -> [Char]
drawTikZ (T.Node a []) =
  "node {" ++ show a ++ "};"
drawTikz (T.Node a b) =
  "node {" ++ show a ++ "} " ++ (L.foldl (++) "" $ drawChild <$> b)
drawChild x = "child {" ++ drawTikz x ++ "}"


drawTikz2 :: Show a => (T.Tree a) -> [Char]
drawTikZ2 (T.Node a []) =
  "[." ++ show a ++ " ]"
drawTikz2 (T.Node a b) =
  "[." ++ show a ++ " " ++ (L.foldl (++) "" $ drawChild2 <$> b) ++ " ]"
drawChild2 x = "[" ++ drawTikz2 x ++ " ]"


--All injective functions from one list to another
injectivesNoCheck [] l = [[]] --the empty function!
injectivesNoCheck _ [] = [] --no functions!
injectivesNoCheck (h:t) s2 =
  [ (h,a):x | a <- s2, x <- injectivesNoCheck t (L.delete a s2) ]

injectives x y
  | L.length x > L.length y = [] --no functions!
  | otherwise = injectivesNoCheck x y



injectivesT [] _ =  T.Node[][] --the empty function
injectivesT (a:b) l =
  T.Node [] $
  (\(h,t)->
      (injectivesT b t) >>= (\x-> T.Node ((a,h):x) [])
  )
  <$> deleteOne l



--Hybrid approach: make a selection of the first [n1,n2,...] elements
(<$$>) f l = (\x-> f <$> x) <$> l
hybridT :: Eq a => [Int] -> [a] -> T.Tree [a]
hybridT [] _ = T.Node [] []
hybridT [n] l = snd <$$> injectivesT [1..n] l
hybridT (n1:ns) l
  | n1 > 0  =
      let deleted = snd <$$> injectivesNoCheck [1..n1] l in
        T.Node [] $ (\x-> (hybridT ns (l L.\\ x) >>= (\y-> T.Node (x ++ y) []))) <$> deleted
  | otherwise =
      hybridT ns l

countLeaves :: (T.Tree a) -> Int
countLeaves (T.Node _ []) = 1
countLeaves (T.Node _ x)  = L.foldl (+) 0 (L.map countLeaves x)

data HanoiBoard = A | B | C deriving (Ord, Show, Eq)
hanoiComplement x y = L.head ([A,B,C] L.\\ [x,y])

hanoiSolve :: (Eq a, Num a) =>
              a -> HanoiBoard -> HanoiBoard -> [(HanoiBoard, HanoiBoard)]
hanoiSolve 1 x y = [(x,y)]
hanoiSolve n x y =
  let c = hanoiComplement x y in
    (hanoiSolve (n-1) x c) ++ (hanoiSolve 1 x y) ++ (hanoiSolve (n-1) c y)

hanoiSolveT :: (Eq a, Num a) =>
               a -> HanoiBoard -> HanoiBoard -> T.Tree [(HanoiBoard, HanoiBoard)]
hanoiSolveT 1 x y = T.Node [(x,y)] []
hanoiSolveT n x y =
  let c = hanoiComplement x y in
    T.Node [] [hanoiSolveT (n-1) x c, hanoiSolveT 1 x y, hanoiSolveT (n-1) c y]

--Debugging trick...
myfun a b | trace ("myfun " ++ show a ++ " " ++ show b) False = undefined
myfun a b = a+b



bins :: Eq a => [a] -> [(Int,a)]
bins l =
  L.reverse $ tobins l Nothing [] where
  tobins :: Eq a => [a] -> (Maybe (Int, a)) -> [(Int,a)] ->  [(Int,a)]
  tobins [] Nothing xs = xs
  tobins [] (Just (n,h)) xs = (n,h) : xs
  tobins (h:t) Nothing xs = tobins t (Just (1,h)) xs
  tobins (h1:t) (Just (n,h2)) x2
    | h1 == h2    = tobins t (Just (n+1,h2)) x2
    | otherwise   = tobins t (Just (1,h1)) ((n,h2) : x2)


decimal :: Int -> [Int]
decimal 0 = []
decimal n = (n `mod` 10) : decimal (n `div` 10)
decimate :: [(Int,Int)] -> [Int]
decimate []          = []
decimate ((n,h) : t) = (decimal n) ++ ( h : decimate t)

flatten []           = []
flatten ((n,h) : t ) = n : h : flatten t

--Conway's look and say sequence:
--look_and_say = [1] : [ decimate $ bins x | x <- look_and_say ]
look_and_say l = l : [ flatten $ bins x | x <- look_and_say l]
--ex: L.take 10 look_and_say [1]


combinations [] r
  | r == 0 = [[]]
  | otherwise = []

combinations (h:t) r =
  a ++ combinations t r where
  a = (\x-> h:x) <$> combinations t (r-1);


--Combination tree
allCombinationsT [] = T.Node [] []


allCombinationsT (h:t) =
  T.Node [] $
  [allCombinationsT t >>= (\x-> T.Node (h:x) []),
    allCombinationsT t]

combinationsTaux x ac r
  | r <= 0          = T.Node ac []
  | r > (L.length x)= T.Node [][]
  | otherwise       =
      T.Node ac [combinationsTaux t (h:ac) (r-1), combinationsTaux t ac r] where
      (h:t) = x


-- combinationsT x r =
--   pruneTree $ internal r $ allCombinationsT x
--   where
--     internal r (T.Node x[])
--       | r /= L.length x = T.Node [][]
--       | otherwise  = T.Node x[]
--     internal r (T.Node x y)
--       | r < L.length x = T.Node [][]
--       | r == L.length x = T.Node x[]
--       | otherwise  = T.Node x (internal r <$> y)

combinationsT x r = pruneTree $ combinationsTaux x [] r


isNullTree (T.Node[][])     = True
isNullTree (T.Node (h:t) _) = False
isNullTree (T.Node[] ts)    = L.foldl (\ac x-> ac && isNullTree x) True ts

pruneTree :: T.Tree [a] -> T.Tree [a]
pruneTree (T.Node x y) =
  T.Node x (L.filter (\x-> not (isNullTree x)) (pruneTree <$> y))

data Binomial = X | Y deriving (Eq,Ord,Show)

binomialTree :: Int -> T.Tree [Binomial]
binomialTree 0 = T.Node [][]
binomialTree n = T.Node [] [left, right] where
  right = (\x-> X:x) <$> b
  left = (\x-> Y:x) <$> b
  b = binomialTree (n-1)

has_exactly_k_Xs :: Int -> Int -> T.Tree [Binomial]
has_exactly_k_Xs _ 0 = T.Node [][]
has_exactly_k_Xs 0 n = T.Node [ Y | _ <- [1..n]] []
has_exactly_k_Xs k n
  | k > n = T.Node [][]
  | k == n = T.Node [ X | _ <- [1..n]] []
  | otherwise =
      T.Node [] [left, right] where
      left = (\x-> X:x) <$> bl
      right = (\x-> Y:x) <$> br
      bl = has_exactly_k_Xs (k-1) (n-1)
      br = has_exactly_k_Xs k (n-1)

has_at_least_k_Xs :: Int -> Int -> T.Tree [Binomial]
has_at_least_k_Xs _ 0 = T.Node [][]
has_at_least_k_Xs k n
  | k > n  = T.Node [] []
  | k == n   = T.Node [ X | _ <- [1..n]] []
  | otherwise =
      T.Node [] [left, right] where
      left = (\x-> Y:x) <$> bl
      right = (\x-> X:x) <$> br
      bl = has_at_least_k_Xs k (n-1)
      br = has_at_least_k_Xs (k-1) (n-1)


--A string of digits is called "lucky" if it contains at least one seven:
data DigitToken  = Digit0 | Digit1 | Digit2 | Digit3 | Digit4 | Digit5 | Digit6 | Digit7 | Digit8 | Digit9 deriving (Eq,Show)
--digits = [Digit0 , Digit1 , Digit2 , Digit3 , Digit4 , Digit5 , Digit6 , Digit7 , Digit8 , Digit9]
digits = [Digit3 , Digit5 , Digit7]
type DigitString = [DigitToken]
lucky :: DigitString -> Bool
lucky [] = False
lucky (h:t)
  | h == Digit7  = True
  | otherwise    = lucky t
unluckyDigits = L.delete Digit7 digits
appendDigits :: DigitString -> [DigitToken] -> [DigitString]
appendDigits digits xs = ( : xs) <$> digits
appendDigit :: DigitToken -> DigitString -> DigitString
appendDigit d xs = d : xs

-- unluckyStrings :: [DigitString]
-- unluckyStrings = [] : unluckyStrings >>= appendDigits unluckyDigits
-- luckyStrings :: [DigitString]
-- luckyStrings =
--   [Digit7] :
--   (zip unluckyStrings luckyStrings
--    >>=(
--       \(unluckyString,luckyString) ->
--         (appendDigit Digit7 unluckyString) : (appendDigits digits luckyString)
--       )
--   )
-- appendDigitToNode digit (T.Node xs yss) = T.Node (digit:xs) (appendDigitToNode digit <$> yss)
-- allStringsTree = T.Node [] [appendDigitToNode digit allStringsTree| digit <- digits]

-- unluckyStringsTree =
--   T.Node [] [appendDigitToNode digit allStringsTree | digit <- unluckyDigits]
-- luckyStringsTree =
--   let T.Node _ unluckyStrings = unluckyStringsTree in
--     T.Node [Digit7] $ [appendDigitToNode digit luckyStringsTree| digit <- digits] ++ (appendDigitToNode Digit7 <$> unluckyStrings)


--"Functional" version
luckyStrings 0 = []
luckyStrings n = (appendDigits unluckyDigits =<< luckyStrings (n-1)) ++ (appendDigit Digit7 <$> allStrings (n-1))
--unluckyStrings 0 = [[]]
--unluckyStrings n = appendDigits unluckyDigits =<< unluckyStrings (n-1)
allStrings 0 = [[]]
allStrings n = appendDigits digits =<< allStrings (n-1)

appendDigitToNode :: DigitToken -> T.Tree DigitString -> T.Tree DigitString
appendDigitToNode digit (T.Node xs yss) = T.Node (digit:xs) (appendDigitToNode digit <$> yss)

appendDigitsToNode :: [DigitToken] -> T.Tree DigitString -> [T.Tree DigitString]
appendDigitsToNode digits t = (\d-> appendDigitToNode d t) <$> digits
luckyStringsTree :: Int -> T.Tree DigitString
luckyStringsTree n
  | n <= 1    = T.Node[][T.Node[Digit7][]]
  | otherwise = T.Node [] $ (appendDigitToNode Digit7 $ anyStringsTree (n-1)) : (appendDigitsToNode unluckyDigits $ luckyStringsTree (n-1))
-- unluckyStringsTree 0 = T.Node [][]
-- unluckyStringsTree n = T.Node [] $ (appendDigitsToNode unluckyDigits $ unluckyStringsTree (n-1))
anyStringsTree 0 = T.Node [][]
anyStringsTree n = T.Node [] $ (appendDigitsToNode digits $ anyStringsTree (n-1))




--util
truncateTree 0 (T.Node x _)  = T.Node x []
truncateTree n (T.Node x ys) = T.Node x (truncateTree (n-1) <$> ys)




test :: IO ()
test =
  do
    putStr $ T.drawTree $ permutationsT ['a','b','c']
    putStr $ T.drawTree $ show <$> injectivesT [1,2,3] ['a','b','c','d']
    putStr $ T.drawTree $ show <$> hanoiSolveT 3 A B
    putStr $ T.drawTree $ show <$> binomialTree 2
    putStr $ drawTikz $ show <$> has_at_least_k_Xs 1 4
--    putStr $ show $ L.take 3 $ (T.levels allStringsTree)
    putStr $ drawTikz $ has_at_least_k_Xs 1 3
    return()
