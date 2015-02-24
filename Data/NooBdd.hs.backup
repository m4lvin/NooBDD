module Data.NooBdd (
  -- types:
  Bdd, Assignment,
  -- creation:
  top, bot, var, node,
  -- combination and manipulation:
  neg, con, dis, imp, equ, xor, conSet, disSet, xorSet,
  forall, forallSet, exists, existsSet,
  restrict, restrictSet,
  gfp,
  -- get satisfying assignments:
  allSats, allSatsWith, anySat, anySatWith, satCountWith,
  -- visualization:
  genGraph, showGraph,
  -- internal tools:
  compress
  ) where

import Data.List
import System.Process
import System.IO

data Bdd = Top | Bot | Node Int Bdd Bdd deriving (Show,Eq)

top :: Bdd
top = Top

bot :: Bdd
bot = Bot

var :: Int -> Bdd
var n = Node n Bot Top

node :: Int -> Bdd -> Bdd -> Bdd
node v a b = Node v a b

neg :: Bdd -> Bdd
neg Top = Bot
neg Bot = Top
neg (Node n lhs rhs) = Node n (neg lhs) (neg rhs)

con :: Bdd -> Bdd -> Bdd
con Bot _   = Bot
con _   Bot = Bot
con Top Top = Top
con x   Top = x
con Top x   = x
con a b     = apply con a b

dis :: Bdd -> Bdd -> Bdd
dis Top _   = Top
dis _   Top = Top
dis Bot Bot = Bot
dis x   Bot = x
dis Bot x   = x
dis a b     = apply dis a b

imp :: Bdd -> Bdd -> Bdd
imp Bot _   = Top
imp _   Top = Top
imp Top x   = x
imp x   Bot = neg x
imp a   b   = apply imp a b

equ :: Bdd -> Bdd -> Bdd
equ Bot x   = neg x
equ x   Bot = neg x
equ Top x   = x
equ x   Top = x
equ a   b   = apply equ a b

xor :: Bdd -> Bdd -> Bdd
xor Bot x   = x
xor x   Bot = x
xor Top x   = neg x
xor x   Top = neg x
xor a   b   = apply xor a b

apply :: (Bdd -> Bdd -> Bdd) -> Bdd -> Bdd -> Bdd
apply f as@(Node a alhs arhs) bs@(Node b blhs brhs) =
  compress $ case (compare a b) of
       EQ -> (Node a (f alhs blhs) (f arhs brhs))
       LT -> (Node a (f alhs bs) (f arhs bs))
       GT -> (Node b (f as blhs) (f as brhs))
apply _ _ _ = error "apply should not be called on constants!";

compress :: Bdd -> Bdd
compress Top = Top
compress Bot = Bot
compress (Node k lhs rhs) =
  if (lhs == rhs) then (compress lhs) else (Node k (compress lhs) (compress rhs))

conSet :: [Bdd] -> Bdd
conSet [] = Top
conSet (b:bs) =
  if elem Bot (b:bs)
    then Bot
    else foldl con b bs
    
disSet :: [Bdd] -> Bdd
disSet [] = Bot
disSet (b:bs) =
  if elem Top (b:bs)
    then Top
    else foldl dis b bs

xorSet :: [Bdd] -> Bdd
xorSet [] = Bot
xorSet (b:bs) = foldl xor b bs

forall :: Int -> Bdd -> Bdd
forall _ Top = Top
forall _ Bot = Bot
forall n (Node m lhs rhs) =
  if (n==m) then (con lhs rhs) else (Node m (forall n lhs) (forall n rhs))

forallSet :: [Int] -> Bdd -> Bdd
forallSet _ Top = Top
forallSet _ Bot = Bot
forallSet ns (Node n lhs rhs) =
  if (elem n ns)
    then (con (forallSet ns lhs) (forallSet ns rhs))
    else (Node n (forallSet ns lhs) (forallSet ns rhs))

restrict :: Bdd -> (Int,Bool) -> Bdd
restrict Top _ = Top
restrict Bot _ = Bot
restrict (Node n lhs rhs) (m,b) =
  compress $ case ((n==m),b) of
    (True,False) -> lhs
    (True,True) -> rhs
    (False,_) -> (Node n (restrict lhs (m,b)) (restrict rhs (m,b)))

restrictSet :: Bdd -> [(Int,Bool)] -> Bdd
restrictSet Top _ = Top
restrictSet Bot _ = Bot
restrictSet (Node n lhs rhs) list =
  compress $ case (lookup n list) of
    Nothing    -> (Node n (restrictSet lhs list) (restrictSet rhs list))
    Just False -> restrictSet lhs list
    Just True  -> restrictSet rhs list

exists :: Int -> Bdd -> Bdd
exists _ Top = Top
exists _ Bot = Bot
exists n (Node m lhs rhs) =
  if (n==m) then (dis lhs rhs) else (Node m (exists n lhs) (exists n rhs))

existsSet :: [Int] -> Bdd -> Bdd
existsSet _ Top = Top
existsSet _ Bot = Bot
existsSet ns (Node n lhs rhs) =
  if (elem n ns)
    then (dis (existsSet ns lhs) (existsSet ns rhs))
    else (Node n (existsSet ns lhs) (existsSet ns rhs))

-- greatest fixedpoint for a given operator
gfp :: (Bdd -> Bdd) -> Bdd
gfp operator = gfpStep operator top (operator top) where
  gfpStep :: (Bdd -> Bdd) -> Bdd -> Bdd -> Bdd
  gfpStep operator current next =
    if (current == next)
      then current
      else gfpStep operator next (operator next)

type Assignment = [(Int,Bool)] -- TODO: Ord instance, to beautify allSatsWith

-- get all partial "just enough" assignments
allSats :: Bdd -> [Assignment]
allSats Top = [ [] ]
allSats Bot = [    ]
allSats (Node n lhs rhs) =
  [ ((n,False):rest) | rest <- allSats lhs ] ++
  [ ((n,True ):rest) | rest <- allSats rhs ]

-- given a set of all vars, complete an assignment
completeAss :: [Int] -> Assignment -> [Assignment]
completeAss allvars ass =
  if (addvars ass == [])
    then [ass]
    else concat $ map (completeAss allvars) (extend ass (head (addvars ass)))
  where
    addvars s = allvars \\ (sort $ map fst s)
    extend s v = [ ((v,False):s), ((v,True):s) ]
  
-- given a set of all vars, get all complete assignments
-- (including those which might have disappeared in the BDD)
allSatsWith :: [Int] -> Bdd -> [Assignment]
allSatsWith allvars b = concat $ map (completeAss allvars) (allSats b) where

-- find the lexicographically smallest satisfying assignment
anySat :: Bdd -> Maybe Assignment
anySat Top = Just []
anySat Bot = Nothing
anySat (Node v lhs rhs) = 
  case lhs of
       Top  -> Just []
       Bot  -> Just ((v,True ):rest) where (Just rest) = (anySat rhs)
       _    -> Just ((v,False):rest) where (Just rest) = (anySat lhs)

anySatWith :: [Int] -> Bdd -> Maybe Assignment
anySatWith _       Bot = Nothing
anySatWith allvars b   = Just $ head $ completeAss allvars ass where (Just ass) = (anySat b)

-- given a set of all vars, get the number of satisfying assignments
-- this is not efficient and could be done without actually generating them!
satCountWith :: [Int] -> Bdd -> Int
satCountWith allvars b = length (allSatsWith allvars b)

type Note = [Int]
data AnnotatedBdd = ATop Note | ABot Note | ANode Int AnnotatedBdd AnnotatedBdd Note deriving (Show,Eq)

varsOf :: Bdd -> [Int]
varsOf Top = []
varsOf Bot = []
varsOf (Node v lhs rhs) = sort $ nub $ (v:(varsOf lhs) ++ (varsOf rhs))

noteOf :: AnnotatedBdd -> Note
noteOf (ABot n) = n
noteOf (ATop n) = n
noteOf (ANode _ _ _ n) = n

annotate :: Bdd -> AnnotatedBdd
annotate Bot = ABot [0]
annotate Top = ATop [1]
annotate (Node k lhs rhs) = ANode k (annotate lhs) (annotate rhs) $
  if ( noteOf (annotate lhs) == noteOf (annotate rhs) )
    then noteOf (annotate lhs)
    else (k:(noteOf $ annotate lhs)) ++ (k:(noteOf $ annotate rhs))

genGraph :: Bdd -> String
genGraph (Bot) = "digraph g { Bot [label=\"0\",shape=\"box\"]; }"
genGraph (Top) = "digraph g { Top [label=\"1\",shape=\"box\"]; }"
genGraph b = "strict digraph g {\n" ++ (genGraphStep (annotate b)) ++ sinks ++ rankings ++ "}"
  where
    genGraphStep (ANode v lhs rhs l) =
      "n"++(lp l)++" [label=\""++(show v)++"\",shape=\"circle\"];\n"
      ++ case lhs of
	(ATop _) -> "n"++(lp l)++" -> Top [style=dashed];\n"
	(ABot _) -> "n"++(lp l)++" -> Bot [style=dashed];\n"
	(ANode _ _ _ l') -> "n"++(lp l)++" -> n"++(lp l')++" [style=dashed];\n" ++ genGraphStep lhs
      ++ case rhs of
	(ATop _) -> "n"++(lp l)++" -> Top;\n"
	(ABot _) -> "n"++(lp l)++" -> Bot;\n"
	(ANode _ _ _ l') -> "n"++(lp l)++" -> n"++(lp l')++";\n" ++ genGraphStep rhs
    genGraphStep _ = ""
    sinks = "Bot [label=\"0\",shape=\"box\"];\n" ++ "Top [label=\"1\",shape=\"box\"];\n"
    rankings = concat [ "{ rank=same; "++(sepBy " " (nub $ nodesOf v (annotate b)))++" }\n" | v <- varsOf b ]
    nodesOf _ (ABot _) = []
    nodesOf _ (ATop _) = []
    nodesOf v (ANode v' lhs rhs l) = if (v==v') then ["n"++lp l] else ((nodesOf v lhs) ++ (nodesOf v rhs))
    sepBy _ [] = ""
    sepBy _ [x] = x
    sepBy c (x:xs) = x++c++(sepBy c xs)
    lp l = concat $ map show l

showGraph :: Bdd -> IO ()
showGraph b = do
  -- _ <- system ("echo '"++string++"' | dot -Tx11")
  (inp,_,_,pid) <- runInteractiveProcess "/usr/bin/dot" ["-Tx11"] Nothing Nothing
  hPutStr inp (genGraph b)
  hFlush inp
  hClose inp
  _ <- waitForProcess pid
  return ()

-- TODO:
-- randomSat -- with correct probabilities, returning IO Bdd
-- boolean apply and forall in parallel -- for optimization?
