module Data.NooBdd.Tests (
  testResults,
  slideshow
  ) where

import Data.NooBdd
import System.Random

varmax :: Int
varmax = 10

getRandomInt :: Int -> IO Int
getRandomInt n = getStdRandom (randomR (0,n))

buildRandBdd :: Int -> IO Bdd 
buildRandBdd v =
  if (v >= varmax)
    then do
      n <- getRandomInt 1
      case n of
	0 -> do return bot
	_ -> do return top
    else do
      n <- getRandomInt 7
      case n of 
	0 -> do return bot
	1 -> do return top
	_ -> do plusv <- getRandomInt (max 0 (varmax-v))
		let myv = v + plusv
		lhs <- buildRandBdd (myv+1)
		rhs <- buildRandBdd (myv+1)
		return $ compress (node v lhs rhs)

slideshow  :: Int -> IO ()
slideshow n = let 
  slide _ = do
    b <- buildRandBdd 0
    _ <- showGraph b
    return ()
  in do
    _ <- mapM_ slide [1..n]
    return ()
  
testResult :: IO Bool
testResult = do
  a <- buildRandBdd 0
  b <- buildRandBdd 0
  c <- buildRandBdd 0
  d <- buildRandBdd 0
  let result = and [ doubleNeg a, deMorgan a b, threeMorgan a b c, equImpCon a b c d, satsValid a ]
  if (not result) then putStrLn ("\nerror: "++(show a)) else putStr "."
  return $ result
  
testResults :: Int -> IO Bool
testResults n =  do
  results <- mapM (\_ -> testResult) [1..n]
  return $ and results

doubleNeg :: Bdd -> Bool
doubleNeg b = (==) b (neg $ neg $ b)

deMorgan :: Bdd -> Bdd -> Bool
deMorgan a b = (==) (con a b) (neg $ dis (neg $ a) (neg $ b))

threeMorgan :: Bdd -> Bdd -> Bdd -> Bool
threeMorgan a b c = (==) (neg $ conSet [a, b, c]) (disSet [neg $ a, neg $ b, neg $ c])

equImpCon :: Bdd -> Bdd -> Bdd -> Bdd -> Bool
equImpCon a b c d = (==) (imp a (imp b (imp c d))) (imp (conSet [a,b,c]) d)

satsValid :: Bdd -> Bool
satsValid b = and [ top == restrictSet b ass | ass <- allSats b ]
