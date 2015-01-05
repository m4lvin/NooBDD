module NooBdd (
  -- type:
  Bdd,
  Assignment,
  -- creation:
  top,
  bot,
  var,
  -- combination and manipulation:
  neg,
  con,
  dis,
  imp,
  equ,
  forall,
  forallSet,
  exists,
  existsSet,
  restrict,
  restrictSet,
  -- get satisfying assignments:
  allSats,
  allSatsWith,
  anySat,
  anySatWith,
  -- visualization
  genGraph,
  showGraph
  -- ...
  ) where

import Data.List
import System.Process

data Bdd = Top | Bot | Node Int Bdd Bdd deriving (Show,Eq)

top :: Bdd
top = Top

bot :: Bdd
bot = Bot

var :: Int -> Bdd
var n = Node n Bot Top

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
  if (lhs == rhs) then lhs else (Node k (compress lhs) (compress rhs))

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
  
example :: Int -> Bdd
example 0 = equ (con (var 1) (dis (neg $ var 1) (var 0))) (con (var 0) (var 1))
example _ = Bot

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

genGraph :: Bdd -> String
genGraph Bot = "digraph g { Bot [label=\"0\",shape=\"box\"]; }"
genGraph Top = "digraph g { Top [label=\"1\",shape=\"box\"]; }"
genGraph b = "digraph g {\n" ++ (genGraphStep "" b) ++ sinks ++ "}"
  where
    genGraphStep _ Top = ""
    genGraphStep _ Bot = ""
    genGraphStep p (Node v lhs rhs) =
      "v"++(show v)++"x"++p++" [label=\""++(show v)++"\",shape=\"circle\"];\n"
      ++ case lhs of
	Top -> "v"++(show v)++"x"++p++" -> Top [style=dashed];\n"
	Bot -> "v"++(show v)++"x"++p++" -> Bot [style=dashed];\n"
	(Node v' _ _) -> "v"++(show v)++"x"++p++" -> v"++(show v')++"x"++('0':p)++" [style=dashed];\n"
	++ genGraphStep ('0':p) lhs
      ++ case rhs of
	Top -> "v"++(show v)++"x"++p++" -> Top;\n"
	Bot -> "v"++(show v)++"x"++p++" -> Bot;\n"
	(Node v' _ _) -> "v"++(show v)++"x"++p++" -> v"++(show v')++"x"++('1':p)++";\n"
	++ genGraphStep ('1':p) rhs
    sinks = "Bot [label=\"0\",shape=\"box\"];\n" ++ "Top [label=\"1\",shape=\"box\"];\n"

showGraph :: Bdd -> IO ()
showGraph b = do
  let string = genGraph b
  _ <- system ("echo '"++string++"' | dot -Tx11")
  return ()

-- TODO:

-- conSet
-- disSet
-- forallSet
-- existsSet

-- satcount

-- IDEAS:
-- randomSat -- with correct probabilities, returning IO Bdd
-- boolean apply and forall in parallel -- for optimization?
