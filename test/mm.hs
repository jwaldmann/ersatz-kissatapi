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

{-# language TypeApplications, OverloadedStrings #-}

import Prelude hiding ((&&),(||),not, or, and,all,any )
import qualified Prelude
import Ersatz
import Ersatz.Solver.Kissat.API
import Control.Monad (replicateM, forM_)
import Text.Printf

main :: IO ()
main = down 2

down :: Int -> IO ()
down dim = do
  let go muls = mainf dim muls >> go (muls - 1)
  go $ dim^3

mainf :: Int -> Int -> IO ()
mainf dim muls = do
  out <- solveWith (kissatapi_with [ Configuration "sat" ]) $ do
    let mat = replicateM dim $ replicateM dim $ exists @Bit
    abcs <- replicateM muls $ replicateM 3 mat
    let range = [0 .. dim-1]
    assert
      $ flip all (replicateM 6 range)
      $ \ [ai, aj, bi, bj, ci, cj] ->
          let want = ai == ci && aj == bi && bj == cj
              have = xors $ do
                [a,b,c] <- abcs
                return $ a!!ai!!aj && b!!bi!!bj && c!!ci!!cj
          in  encode want === have
    return abcs
  case out of
    (Satisfied, Just abcs) -> do
      forM_ (zip [1 :: Int ..] abcs) $ \ (k, [a,b,c]) -> do
        printf "%d\n" k
        forM_ [0..dim-1] $ \ i -> do
          printf "  %s  %s  %s\n" (srow i a) (srow i b) (srow i c) 
      
xors = foldr1 xor

srow i m = show $ map fromEnum $ m !! i
