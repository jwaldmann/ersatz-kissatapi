-- | compute oscillator for Conway's game of life, 
-- cf. http://www.conwaylife.com/wiki/Category:Oscillators
-- example usage: ./dist/build/Life/Life 3 9 9 20
-- arguments are: period, width, height, number of life start cells

{-# language PatternSignatures #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language TupleSections #-}
{-# language DataKinds #-}

import Prelude hiding ((&&),(||),not, or, and,all,any )
import qualified Prelude
import Ersatz
import qualified Ersatz.Relation as R
import qualified Data.Array as A
import qualified Ersatz.Counting as C
import qualified Ersatz.Number.Binary as B
import qualified Ersatz.Number.Unary as U
import qualified Ersatz.Number.Class as C
import Ersatz.Solver.Kissat.API
import Control.Applicative
import Control.Monad
import Data.List ( tails, transpose )

import System.Environment


import Control.Monad ( guard, when, forM, foldM, void )
import System.Environment
import Data.Ix ( range, inRange )

main :: IO ()
main = void $ do
    argv <- getArgs
    (Satisfied, Just gs) <-
      solveWith (kissatapi_with [ Configuration "sat" ]) $ case map read argv of
        []             -> osc 3 9 9 (Just 20)
        [ p, w       ] -> osc p w w Nothing
        [ p, w, h    ] -> osc p w h Nothing
        [ p, w, h, c ] -> osc p w h $ Just c
    forM ( zip [ 0..  ] gs ) $ \ (t, g) -> do
        putStrLn $ unwords [ "time", show t ]
        printA g

printA :: A.Array (Int,Int) Bool -> IO ()
printA a = putStrLn $ unlines $ do
         let ((u,l),(o,r)) = A.bounds a
         x <- [u .. o]
         return $ unwords $ do 
             y <- [ l ..r ]
             return $ case a A.! (x,y) of
                  True -> "O " ; False -> ". "

instance (A.Ix a, A.Ix b) => Equatable (R.Relation a b) where
  r === s = encode (R.bounds r == R.bounds s)
    && R.elems r === R.elems s

instance (A.Ix a, A.Ix b) => Orderable (R.Relation a b) where
  r <? s = encode (R.bounds r == R.bounds s)
    && R.elems r <? R.elems s

osc :: MonadSAT s m
    => Int -> Int -> Int -> Maybe Int
    -> m  [ R.Relation Int Int ] 
osc p w h mc = do
  g0 <- R.relation ((1,1),(w,h))
  case mc of
    Just c -> assert $ C.atmost c $ R.elems g0
    Nothing -> return ()
  let gs = take (p+1) $ iterate next g0
  assert (head gs === last gs)
  assert $ all bordered gs
  -- assert $ all (g0 <?) $ init $ tail gs
  assert $ and $ do
    t <- filter isPrime [ 2 .. p ]
    let (d,m) = divMod p t
    return $ if 0 == m then g0 /== gs!!d else true
  return gs

isPrime n = all (\t -> 0 /= mod n t) $ takeWhile (\t -> t*t <= n) $ 2 : [3,5..]

next :: R.Relation Int Int -> R.Relation Int Int
next g =
  let fc :: [[ B.Binary 3 ]]
      fc = field_count $ to_field g
  in  R.build (R.bounds g) $ do
    ((i,j),x) <- R.assocs g
    let c = fc !! (i-1) !! (j-1)
        v = c === encode 3 ||  (x &&  c === encode 4)
    return ((i,j),v)

to_field g = do
  let ((u,l),(o,r)) = R.bounds g
  i <- [u..o]
  return $ do j <- [l..r]; return $ g R.! (i,j)
         
field_count xss =
  let w = length $ head xss
  in  triplets (replicate w $ encode 0) (zipWith (+))
      $ map row_count xss

row_count xs =
  triplets (encode 0) (+) $ map C.fromBit xs

single :: Bit -> Bits
single x = Bits [x]

-- | triplets z f [x0,x1,x2,x3...] =
-- [f z (f x0 x1), f(f x0 x1)x2, f x1 f(x2 x3), f (f x2 x3) x4 .. ]
triplets :: a -> (a->a->a) -> [a] -> [a]
triplets z f xs = take (length xs) $ do
  let get i = if i < 0 || i >= length xs then z else xs !! i
  i <- [0, 2 .. length xs - 1]
  let -- this computation is shared, and that's the point:
      p = f (get i) (get $ i+1)
  [ f (get $ i-1) p, f p (get $ i+2) ]


bordered_naive g = 
  let ((u,l),(d,r)) = R.bounds g
  in
      ( flip all [u..d] $ \ x -> flip all [l, r] $ \ y -> not $ g R.! (x,y) )
   && ( flip all [u,d] $ \ x -> flip all [l .. r] $ \ y -> not $ g R.! (x,y) )

bordered g = and $ do
  let ((u,l),(d,r)) = R.bounds g
  edge <- [ map (u,) [l..r] , map (d,) [l..r]
           , map (,l) [u..d] , map (,r) [u..d]
           ]
  block <- map (take 3) $ tails $ map (g R.!) edge
  guard $ length block == 3
  return $ not $ and block

next_simple g = 
  let bnd = R.bounds g
      neighbours (i,j) = do
            i' <- [ i-1, i, i+1 ]
            j' <- [ j-1, j, j+1 ]
            guard $ i /= i' || j /= j'
            return $ if A.inRange bnd (i',j') 
               then g R.! (i', j')
               else false
  in  R.build bnd $ do
    (i,x) <- R.assocs g
    return (i, step x $ neighbours i)

-- | CNF 7756 vars 29693 clauses  37 sec
step_naive x xs = let n = sumBits xs in (x && n === encode 2) || (n === encode 3)
-- | CNF 6361 vars 35108 clauses   7 sec
step_unary x xs = let cs = census xs in (x && cs !! 2)        || cs !! 3
-- | CNF 11953 vars 54222 clauses  1min52
step_count x xs = x && C.exactly 2 xs || C.exactly 3 xs
-- | CNF 6475 vars 26312 clauses  21sec
step_binary x xs =
  let n :: B.Binary 2; n = sum $ map (\ x -> B.fromBits $ Bits [x]) xs
  in  x && (n === encode 2) || (n === encode 3)

step = step_unary



-- | census xs !! k <=> sumBits xs == k
census [] = [true]
census (x:xs) =
  let cs = census xs
  in  zipWith (\ a b -> choose a b x)
        (cs <> [false]) ([false] <> cs)

