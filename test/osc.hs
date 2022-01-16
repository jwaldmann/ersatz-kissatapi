-- | compute oscillator for Conway's game of life, 
-- cf. http://www.conwaylife.com/wiki/Category:Oscillators
-- example usage: ./dist/build/Life/Life 3 9 9 20
-- arguments are: period, width, height, number of life start cells

{-# language PatternSignatures #-}
{-# language FlexibleContexts #-}

import Prelude hiding ((&&),(||),not, or, and,all,any )
import qualified Prelude
import Ersatz
import qualified Ersatz.Relation as R
import qualified Data.Array as A
import qualified Ersatz.Counting as C
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
      solveWith kissatapi $ case map read argv of
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
                  True -> "* " ; False -> ". "

instance (A.Ix a, A.Ix b) => Equatable (R.Relation a b) where
  r === s = encode (R.bounds r == R.bounds s)
    && R.elems r === R.elems s

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
  assert $ and $ do
    t <- [1..p-1]
    return $ encode (0 == mod p t) ==> g0 /== gs !! t
  return gs

bordered g = 
  let ((u,l),(d,r)) = R.bounds g
  in
      ( flip all [u..d] $ \ x -> flip all [l, r] $ \ y -> not $ g R.! (x,y) )
   && ( flip all [u,d] $ \ x -> flip all [l .. r] $ \ y -> not $ g R.! (x,y) )


next g = 
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

step x xs =
  let keep  = x && C.exactly 2 xs
      birth =      C.exactly 3 xs
  in  keep || birth

