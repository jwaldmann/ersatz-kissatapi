-- matrix multiplication schema in characteristic 2,
-- see Kauers and Moosbauer https://arxiv.org/abs/2210.04045

-- known results:      
-- dim = 2 : muls =  7   [8] Strassen 1969
-- dim = 3 : muls = 23   [4] Ladermann 1976
-- dim = 4 : muls = 47   [2] FBHHRBNRSSSHK 2022
-- dim = 5 : muls = 95       Kauers and Moosbauer 2022

-- program below finds:
-- dim = 2 : muls =  7   very fast
-- dim = 3 : muls = 25              CNF 34912 vars 137782 clauses
-- dim = 4 : muls =    
-- dim = 5 : muls =    

{-# language TypeApplications, OverloadedStrings, LambdaCase #-}

import Prelude hiding ((&&),(||),not, or, and,all,any )
import qualified Prelude
import Ersatz
import Ersatz.Solver.Kissat.API
import Control.Monad (replicateM, forM_, when)
import Text.Printf
import System.IO
import System.Environment

main :: IO ()
main = getArgs >>= \ case
  [] -> down 2
  [d] -> down (read d)

down :: Int -> IO ()
down dim = do
  let go muls = mainf dim muls >> go (muls - 1)
  hSetBuffering stdout LineBuffering
  go $ dim^3

mainf :: Int -> Int -> IO ()
mainf dim muls = do
  out <- solveWith (kissatapi_with [ Configuration "sat" ]) $ do
    let mat = replicateM dim $ replicateM dim $ exists @Bit
    abcs <- replicateM muls $ replicateM 3 mat
    when False $ assert $ flip all (zip abcs $ tail abcs) $ \ (x, y) ->
      head x <=? head y
    let range = [0 .. dim-1]
    forM_ (replicateM 6 range) $ \ [ai,aj, bi,bj, ci,cj] -> do
          let want = ai == ci && aj == bi && bj == cj
              have = xors $ do
                [a,b,c] <- abcs
                return $ a!!ai!!aj && b!!bi!!bj && c!!ci!!cj
          assert $ encode want === have
    return abcs
  case out of
    (Satisfied, Just abcs) -> do
      printf "======== dim %d muls %d\n" dim muls
      forM_ (zip [1 :: Int ..] abcs) $ \ (k, [a,b,c]) -> do
        printf "%d\n" k
        forM_ [0..dim-1] $ \ i -> do
          printf "  %s  %s  %s\n" (srow i a) (srow i b) (srow i c) 
      
xors = foldr1 xor

bfoldr1 op xs =
  let go [x] = x
      go (x:y:zs) = go (zs <> [op x y])
  in  go xs

srow i m = show $ map fromEnum $ m !! i
