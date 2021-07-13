-- MOURRE Grégoire
-- Arbres binaires de propositions

----------------------------------------------------------------
-- Question 1
----------------------------------------------------------------

-- Tformule
data Tformule = Val Bool
 | Var String
 | Non Tformule
 | Et Tformule Tformule
 | Ou Tformule Tformule
 | Impl Tformule Tformule
 | Equiv Tformule Tformule
 deriving (Show, Eq)

-- DecisionTree pour la question 1
data DecisionTree = Leaf Bool | Node String DecisionTree DecisionTree
 deriving Show

-- Exemple du sujet (pour les tests)
exemple :: Tformule
exemple = Et (Equiv (Var "P1") (Var "Q1")) (Equiv (Var "P2") (Var "Q2"))

-- Fonction qui renvoie l'ensemble des variables d'une formule
varNames :: Tformule -> [String]
varNames (Var str) = [str]
varNames (Non f) = varNames f
varNames (Et f1 f2) = varNames f1 ++ varNames f2
varNames (Ou f1 f2) = varNames f1 ++ varNames f2
varNames (Impl f1 f2) = varNames f1 ++ varNames f2
varNames (Equiv f1 f2) = varNames f1 ++ varNames f2
varNames _ = []

-- Fonction qui remplace une variable par une valeur booléenne dans une formule
remplace :: String -> Bool -> Tformule -> Tformule
remplace str bool f@(Var str') = if str == str' then Val bool else f
remplace str bool (Non f) = Non (remplace str bool f)
remplace str bool (Et f1 f2) = Et (remplace str bool f1) (remplace str bool f2)
remplace str bool (Ou f1 f2) = Ou (remplace str bool f1) (remplace str bool f2)
remplace str bool (Impl f1 f2) = Impl (remplace str bool f1) (remplace str bool f2)
remplace str bool (Equiv f1 f2) = Equiv (remplace str bool f1) (remplace str bool f2)
remplace str bool f = f

-- Fonction qui évalue une formule évaluable
eval :: Tformule -> Bool
eval (Val bool) = bool
eval (Non f) = not $ eval f
eval (Et f1 f2) = eval f1 && eval f2
eval (Ou f1 f2) = eval f1 || eval f2
eval (Impl f1 f2) = if eval f1 then eval f2 else True
eval (Equiv f1 f2) = eval f1 == eval f2
eval _ = error "Formule non-évaluable"

-- Fonction qui créé un arbre en remplaçant les variables une à une par False et par True
makeTreeInter :: [String] -> Tformule -> DecisionTree
makeTreeInter [] f = Leaf $ eval f
makeTreeInter (x:xs) f = Node x (makeTreeInter xs $ remplace x False f) (makeTreeInter xs $ remplace x True f)

-- Fonction finale
makeTree :: Tformule -> DecisionTree
makeTree f = makeTreeInter tab f
 where tab = varNames f

----------------------------------------------------------------
-- Question 2
----------------------------------------------------------------

-- Noeud BDD
data BddNode = BddLeaf Int Bool | BddOther Int String Int Int
 deriving Show

-- Fonction qui vérifie si 2 formules sont équivalentes (même si elles ne sont pas encore évaluables)
estEquiv :: Tformule -> Tformule -> Bool
estEquiv (Val bool1) (Val bool2) = bool1 == bool2
estEquiv (Non f1) (Non f2) = let f1' = if estEvaluable f1 then Val $ eval f1 else f1
                                 f2' = if estEvaluable f2 then Val $ eval f2 else f2
                             in estEquiv f1' f2'
estEquiv (Var str1) (Var str2) = str1 == str2
estEquiv (Et f1 f2) (Et g1 g2) = let f1' = if estEvaluable f1 then Val $ eval f1 else f1
                                     f2' = if estEvaluable f2 then Val $ eval f2 else f2
                                     g1' = if estEvaluable g1 then Val $ eval g1 else g1
                                     g2' = if estEvaluable g2 then Val $ eval g2 else g2
                                 in (estEquiv f1' g1' && estEquiv f2' g2') || (estEquiv f1' g2' && estEquiv f2' g1') || and (map (elem (Val False)) [[f1',f2'],[g1',g2']])
estEquiv (Ou f1 f2) (Ou g1 g2) = let f1' = if estEvaluable f1 then Val $ eval f1 else f1
                                     f2' = if estEvaluable f2 then Val $ eval f2 else f2
                                     g1' = if estEvaluable g1 then Val $ eval g1 else g1
                                     g2' = if estEvaluable g2 then Val $ eval g2 else g2
                                 in (estEquiv f1' g1' && estEquiv f2' g2') || (estEquiv f1' g2' && estEquiv f2' g1')
estEquiv (Impl f1 f2) (Impl g1 g2) = let f1' = if estEvaluable f1 then Val $ eval f1 else f1
                                         f2' = if estEvaluable f2 then Val $ eval f2 else f2
                                         g1' = if estEvaluable g1 then Val $ eval g1 else g1
                                         g2' = if estEvaluable g2 then Val $ eval g2 else g2
                                     in (estEquiv f1' g1' && estEquiv f2' g2')
estEquiv (Equiv f1 f2) (Equiv g1 g2) = let f1' = if estEvaluable f1 then Val $ eval f1 else f1
                                           f2' = if estEvaluable f2 then Val $ eval f2 else f2
                                           g1' = if estEvaluable g1 then Val $ eval g1 else g1
                                           g2' = if estEvaluable g2 then Val $ eval g2 else g2
                                       in (estEquiv f1' g1' && estEquiv f2' g2') || (estEquiv f1' g2' && estEquiv f2' g1')
estEquiv _ _ = False

-- Fonction qui détermine si une formule est évaluable
estEvaluable :: Tformule -> Bool
estEvaluable (Val _) = True
estEvaluable (Non f) = estEvaluable f
estEvaluable (Et f1 f2) = estEvaluable f1 && estEvaluable f2
estEvaluable (Ou f1 f2) = estEvaluable f1 && estEvaluable f2
estEvaluable (Impl f1 f2) = if estEvaluable f1 then (if eval f1 == False then True else estEvaluable f2) else (if estEvaluable f2 then eval f2 else False)
estEvaluable (Equiv f1 f2) = estEvaluable f1 && estEvaluable f2
estEvaluable _ = False

----------------------------------------------------------------
-- Premier essai de la question 2
----------------------------------------------------------------

-- makeBDD2 :: Tformule -> [BddNode]
-- makeBDD2 f = map snd $ makeBDDInter f [] (varNames f) 1

-- makeBDDInter :: Tformule -> [(Tformule, BddNode)] -> [String] -> Int -> [(Tformule, BddNode)]
-- makeBDDInter f fTab [] i = case findNum2 f fTab of Just x -> fTab
                                                  -- Nothing -> (f,BddLeaf i $ eval f):fTab
-- makeBDDInter f fTab (x:xs) i = nextNodeT
 -- where
  -- f1 = remplace x False f
  -- f2 = remplace x True f
  -- test1 = findNum2 f1 fTab
  -- j = case test1 of Just o -> o
                    -- Nothing -> i + 1
  -- nextNodeF = if test1 == Nothing
              -- then makeBDDInter f1 ((f, BddOther i x j (-i)):fTab) xs (i + 1)
              -- else let Just num1 = test1 in ((f, BddOther i x num1 (-i)):fTab)
  -- max2 = findMax nextNodeF
  -- test2 = findNum2 f2 nextNodeF
  -- k = case test2 of Just p -> p
                    -- Nothing -> max2 + 1
  -- nextNodeFF = change2 (-i) k nextNodeF
  -- nextNodeT = if test2 == Nothing
              -- then makeBDDInter f2 nextNodeFF xs (max2 + 1)
              -- else nextNodeFF

-- findNum2 :: Tformule -> [(Tformule, BddNode)] -> Maybe Int
-- findNum2 f [] = Nothing
-- findNum2 f ((x1,x2):xs)
 -- | estEquiv f x1 = case x2 of BddOther a b c d -> Just a
                              -- BddLeaf a b -> Just a
 -- | otherwise = findNum2 f xs

-- findMax :: [(Tformule, BddNode)] -> Int
-- findMax [] = 1
-- findMax xs = maximum $ map (\x-> case x of BddLeaf a b -> a
                                           -- BddOther a b c d -> a) $ map snd xs

-- change2 :: Int -> Int -> [(Tformule, BddNode)] -> [(Tformule, BddNode)]
-- change2 i j (a@(f,BddOther b c d e):xs)
 -- | e == i = (f,BddOther b c d j):xs
 -- | otherwise = a:change2 i j xs
-- change2 i j (a@(f,BddLeaf b c):xs) = a:change2 i j xs
-- change2 i j [] = []

----------------------------------------------------------------
-- Question 2 (suite)
----------------------------------------------------------------

-- Fonction finale
makeBDD :: Tformule -> [BddNode]
makeBDD f = formules2 (formules f) (varNames f)

-- Fonction qui construit l'arbre étage par étage en cherchant les numéros des noeuds fils
formules2 :: [[Tformule]] -> [String] -> [BddNode]
formules2 [[f]] [] = [BddLeaf 1 $ eval f] -- cas d'une tautologie
formules2 fs [] = [BddLeaf 1 True, BddLeaf 2 False] -- l'autre cas de base
formules2 (f:fs) (name:names) = tab ++ formules2 fs names
 where
  tab = do
   ff <- f
   let listWithNum = change (f:fs)
   let fFalse = remplace name False ff
   let fTrue = remplace name True ff
   let num = findNum ff (head listWithNum)
   let numFalse = findNum fFalse (head $ tail listWithNum)
   let numTrue = findNum fTrue (head $ tail listWithNum)
   return $ BddOther num name numFalse numTrue

-- Fonction qui créé des listes de listes de formules, représentant les formules non-équivalentes de chaque étage
formules :: Tformule -> [[Tformule]]
formules f = take (length tab + 1) liste
 where
  tab = varNames f
  g 0 = [f]
  g n = fonction $ do
   x <- liste !! (n-1)
   [remplace (tab !! (n-1)) False x, remplace (tab !! (n-1)) True x]
  liste = [g i | i <- [0..]]

-- Fonction qui réduit une liste de formules en supprimant les doublons de formules équivalentes
fonction :: [Tformule] -> [Tformule]
fonction xs = foldr (\y acc -> if not $ or $ map (estEquiv y) acc then y:acc else acc) [last xs] $ init xs

-- Fonction qui trouve le numéro d'une formule équivalentes dans une liste de (Int,Tformule)
findNum :: Tformule -> [(Int,Tformule)] -> Int
findNum f ((x1,x2):xs)
 | estEquiv f x2 = x1
 | otherwise = findNum f xs

-- Fonction qui associe chaque formule d'une [[Tformule]] à un numéro
change :: [[Tformule]] -> [[(Int,Tformule)]]
change xss = changeInter (sum $ map length xss) xss
 where
  changeInter 0 _ = []
  changeInter n (x:xs) = let len = length x in (zip [n,n-1..n-len+1] x) : (changeInter (n-len) xs)

----------------------------------------------------------------
-- Question 3
----------------------------------------------------------------

-- Fonction finale
simplBDD :: Tformule -> [BddNode]
simplBDD = removeNode . simplBDDInter . makeBDD

-- Fonction qui change les numéros des fils de chaque noeud, s'il le faut
simplBDDInter :: [BddNode] -> [BddNode]
simplBDDInter l = foldr (\(x,y) -> changeFils x y) l $ sortBySnd $ simplBDDInt1 l

-- Fonction qui détermine les numéros à changer
-- exemple : (4,3) signifie que les numéros fils des noeuds valant 4 doivent être changés en 3
simplBDDInt1 :: [BddNode] -> [(Int,Int)]
simplBDDInt1 [] = []
simplBDDInt1 (x:xs) = case x of BddOther a _ c d -> if c == d then (a,c):simplBDDInt1 xs else simplBDDInt1 xs
                                _ -> simplBDDInt1 xs

-- Fonction qui trie par rapport au snd du tuple
-- Cela sert dans les cas où on a par exmple [(7,5),(5,2)],
-- où sans la fonction, on se retrouverait avec des 5 à la fin (alors que l'on en veut pas)
sortBySnd :: [(Int,Int)] -> [(Int,Int)]
sortBySnd [] = []
sortBySnd ((x1,x2):xs) = sortBySnd l ++ [(x1,x2)] ++ sortBySnd r
 where
  l = [(a,b) | (a,b) <- xs, b <= x2]
  r = [(a,b) | (a,b) <- xs, b > x2]

-- Fonction qui retire les noeuds qui ne sont plus utiles (après les changements de numéros)
removeNode :: [BddNode] -> [BddNode]
removeNode [] = []
removeNode (n@(BddOther a b c d):xs) = if c == d then removeNode xs else n:removeNode xs
removeNode (x:xs) = x:removeNode xs

-- Fonction qui change les numéros des noeuds
changeFils :: Int -> Int -> [BddNode] -> [BddNode]
changeFils _ _ [] = []
changeFils i j (x:xs) = y:changeFils i j xs
 where y = case x of BddOther a b c d -> let e = if c == i then j else c
                                             f = if d == i then j else d
                                         in BddOther a b e f
                     _ -> x

----------------------------------------------------------------
-- Question 4 & 5
----------------------------------------------------------------

-- Ces questions sont propres à l'oCaml

----------------------------------------------------------------
-- Question 6
----------------------------------------------------------------

-- Fonciton qui vérifie si le BDD simplifié vaut uniquement une BddLeaf
estTautologie :: Tformule -> Bool
estTautologie f = case simplBDD f of [BddLeaf _ True] -> True
                                     [BddLeaf _ False] -> True
                                     _ -> False

----------------------------------------------------------------
-- Question 7
----------------------------------------------------------------

-- Fonction finale
formuleEquiv :: Tformule -> Tformule -> Bool
formuleEquiv f g = testEquivBDD (simplBDD f) (simplBDD g)

-- Fonction finale bis
-- On suppose que les noeuds en tête de liste sont ceux de tête de graphe
testEquivBDD :: [BddNode] -> [BddNode] -> Bool
testEquivBDD xs ys = testEquivBDDTree xs (head xs) ys (head ys)

-- Fonction qui compare les valeurs de chaque noeud, puis les valeurs des fils (et ainsi de suite)
testEquivBDDTree :: [BddNode] -> BddNode -> [BddNode] -> BddNode -> Bool
testEquivBDDTree _ (BddLeaf _ b) _ (BddLeaf _ d) = b == d
testEquivBDDTree xs (BddOther _ b c d) ys (BddOther _ f g h) = (b == f)
                                                            && (testEquivBDDTree xs (findSon c xs) ys (findSon g ys))
                                                            && (testEquivBDDTree xs (findSon d xs) ys (findSon h ys))
testEquivBDDTree _ _ _ _ = False

-- Fonction qui renvoie noeud du fils en fonction de son numéro
findSon :: Int -> [BddNode] -> BddNode
findSon i (n@(BddLeaf a _):xs) = if i == a then n else findSon i xs
findSon i (n@(BddOther a b c d):xs) = if i == a then n else findSon i xs
findSon _ _ = error "BDD invalide !"

-- Pour tester les fonctions
testEquivalence1 :: [BddNode] -- à comparer avec testEquivalence2
testEquivalence1 = [BddOther 10 "P1" 9 8 ,BddOther 9 "Q1" 6 2,BddOther 8  "Q1" 2 6,BddOther 6 "P2" 4 3,BddOther 4 "Q2" 1 2,BddOther 3 "Q2" 2 1,BddLeaf 2 False,BddLeaf 1 True]
testEquivalence2 :: [BddNode] -- à comparer avec testEquivalence1
testEquivalence2 = [BddOther 3  "P1" 2 10,BddOther 2 "Q1" 1 5,BddOther 10 "Q1" 5 1,BddOther 1 "P2" 6 7,BddOther 6 "Q2" 8 5,BddOther 7 "Q2" 5 8,BddLeaf 8 True,BddLeaf 5 False]
testEquivalence3 :: [BddNode] -- exemple du sujet / à comparer à "makeBDD exemple"
testEquivalence3 = [BddOther 10 "P1" 8 9,BddOther 9 "Q1" 7 5,BddOther 8 "Q1" 5 7,BddOther 7 "P2" 6 6,BddOther 6 "Q2" 2 2,BddOther 5 "P2" 3 4,BddOther 4 "Q2" 2 1,BddOther 3 "Q2" 1 2,BddLeaf 2 False,BddLeaf 1 True]
----------------------------------------------------------------
-- Question 8
----------------------------------------------------------------

-- Fonction finale
findTrue :: [BddNode] -> Maybe [(String,Bool)]
findTrue xs = do
 x <- findNumTrue xs
 return $ reverse $ map (\(_,a,b) -> (a,b)) $ findTrueInter x xs

-- Fonction qui remonte l'une des chaines partant de True
findTrueInter :: Int -> [BddNode] -> [(Int,String,Bool)]
findTrueInter start xs = case findFather start xs of Just r@(a,_,_) -> r:findTrueInter a xs
                                                     Nothing -> []

-- Fonction qui trouve le père d'un maillon (permettant de remonter l'une des chaines qui part de True)
findFather :: Int -> [BddNode] -> Maybe (Int,String,Bool)
findFather i ((BddOther a b c d):xs) = if c == i then Just (a,b,False) else
                                       if d == i then Just (a,b,True) else
                                       findFather i xs
findFather _ _ = Nothing

-- Fonction qui trouve le numéro du maillon True (utile pour de commencer la chaine)
findNumTrue :: [BddNode] -> Maybe Int
findNumTrue xs = case l1 of BddLeaf a True -> Just a
                            _ -> next
 where
  l1 = last xs
  l2 = last $ init xs
  next = case l2 of BddLeaf b True -> Just b
                    _ -> Nothing
