module NooBdd where
import Data.List

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
  if (elem n ns) then (con lhs rhs) else (Node n (forallSet ns lhs) (forallSet ns rhs))


restrict :: Bdd -> (Int,Bool) -> Bdd
restrict Top _ = Top
restrict Bot _ = Bot
restrict (Node n lhs rhs) (m,b) =
  compress $ case ((n==m),b) of
    (True,False) -> lhs
    (True,True) -> rhs
    (False,_) -> (Node n (restrict lhs (m,b)) (restrict rhs (m,b)))

exists :: Int -> Bdd -> Bdd
exists _ Top = Top
exists _ Bot = Bot
exists n (Node m lhs rhs) =
  if (n==m) then (dis lhs rhs) else (Node m (forall n lhs) (forall n rhs))

example :: Int -> Bdd
example 0 = equ (con (var 1) (dis (neg $ var 1) (var 0))) (con (var 0) (var 1))
example _ = Bot

type Assignment = [(Int,Bool)] -- TODO: Ord instance, to beautify allSatsWith

-- partial "just enough" assignments
allSats :: Bdd -> [Assignment]
allSats Top = [ [] ]
allSats Bot = [    ]
allSats (Node n lhs rhs) =
  [ ((n,False):rest) | rest <- allSats lhs ] ++
  [ ((n,True ):rest) | rest <- allSats rhs ]

-- complete assignments, given a set of all vars
-- (including those which might have disappeared in the BDD)
allSatsWith :: Bdd -> [Int] -> [Assignment]
allSatsWith b allvars = concat $ map complete (allSats b) where
  complete sat =
    if (addvars sat == [])
      then [sat]
      else concat $ map complete (extend sat (head (addvars sat)))
    where
      addvars s = allvars \\ (sort $ map fst s)
      extend s v = [ ((v,False):s), ((v,True):s) ]

-- TODO:

-- conSet
-- disSet
-- forallSet
-- existsSet
-- restrictSet

-- satcount
-- anysat

-- graphviz

-- IDEAS:
-- randomSat -- with correct probabilities, returning IO Bdd
-- boolean apply and forall in parallel -- for optimization?
