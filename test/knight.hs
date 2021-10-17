{-# language LambdaCase #-}

import Prelude hiding ((&&),(||),not, or, and )
import qualified Prelude
import Ersatz
import Ersatz.Solver.Kissat.API
import Control.Applicative
import Control.Monad
import Data.List ( tails, transpose )

import System.Environment

main = getArgs >>= \ case 
  [w,h] -> run (read w, read h)
  [] -> run (8,8)

run (w,h) = do 
  (Satisfied, Just a) <- solveWith kissatapi $ do 
    let n = w * h
    a <- replicateM n $ replicateM n exists
    assert $ foreach a $ exactly_one
    assert $ foreach (transpose a) $ exactly_one
    assert $ foreach (zip a $ rotate 1 a) $ \ (e,f) ->
      foreach [0 .. n-1] $ \ p -> (e !! p) ==>
         forsome (filter (reaches h p) [0..n-1]) $ \ q -> f!!q
    assert $ a !! 0 !! 0
    return (a :: [[Bit]] )
  putStrLn $ unlines $ do
    x <- [ 0 .. w-1 ]
    return $ unwords $ do
      y <- [ 0 .. h-1 ]
      let c = length $ takeWhile (== False)
             $ transpose a !! (x*h + y)
      return $ fill 3 $ show c

fill k s = replicate (k - length s) ' ' ++ s

foreach xs f = and $ map f xs
forsome xs f = or  $ map f xs

rotate :: Int -> [a] -> [a]
rotate k xs = let ( pre, post ) = splitAt k xs in  post ++ pre

reaches h p q =
  let (px,py) = divMod p h ; (qx,qy) = divMod q h
  in  5 == (px - qx)^2 + (py - qy)^2

exactly_one xs = let (r,c) = count1 xs in r && not c
atleast_one xs = let (r,c) = count1 xs in r || c
atmost_one xs = let (r,c) = count1 xs in not c

-- | one-bit counter, returns result bit and carry
count1 ::  [Bit] -> (Bit,Bit)
count1 [] = (false,false)
count1 [x] = (x,false)
count1 xs =
  let (ys,zs) = splitAt (div (length xs) 2) xs
      (rl,cl) = count1 ys ; (rr,cr) = count1 zs
  in  (rl || rr, cl || cr || (rl && rr))

