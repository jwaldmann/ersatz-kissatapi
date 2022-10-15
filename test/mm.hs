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
import qualified Data.Bool
import qualified Prelude
import Ersatz hiding (Run)
import Ersatz.Solver.Kissat.API
import Control.Monad (replicateM, forM_, when)
import Text.Printf
import System.IO
import System.Environment
import Data.Time.Clock
import qualified Data.Map as M
import Data.Text (Text)
import Control.Monad.State (StateT)
import System.Random
import Control.Timeout
import Control.Concurrent.Async
import System.IO

main :: IO ()
main = getArgs >>= \ case
  [] -> down 2 Nothing
  [d] -> down (read d) Nothing
  [d, m] -> down (read d) (Just $ read m)
  [ "walk", d, m ] ->
    walk_from od0 ov0 $ \ ov -> mainfor ov (read d) ( read m)

down :: Int -> Maybe Int -> IO ()
down dim mmuls = do
  let go muls = mainf dim muls >>= \ case
        Nothing -> printf "no solution for dim = %d, mmuls = %d\n" dim muls
        Just _ -> go (muls - 1)
  hSetBuffering stdout LineBuffering
  go $ maybe (dim^3 ) id mmuls


walk_from :: OD -> OV -> (OV -> IO r) -> IO ()
walk_from od ov0 action = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering
  let work c ov =  do
          o2 <- changes c od ov
          run o2 action
  let p = 16 
  Just r0 <- bestof Nothing p $ work 1 ov0
  let go c r1 = do
        mr <- bestof (Just $ val r1) p $ work c (ov r1)
        case mr of
          Just (r2, _) | val r2 < val r1 -> do
            printf "best %s, this %s\n" (show r1) (show r2)
            go 1 r2
          _ -> do
            printf "keep best %s, increase c to %d\n" (show r1) (c+1)
            go (c+1) r1
  go (1::Int) $ fst r0

bestof mto k action = do
  as <- mapM async $  replicate k $ 
    ( case mto of
      Nothing -> (Just <$>)
      Just to -> timeout to
      ) action
  snd <$> waitAnyCancel as

changes 0 od ov = return ov
changes c od ov = change od ov >>= \ ov' -> changes (c-1) od ov'

change od ov = do
  (k,bnd@(lo,hi)) <- pick od
  v' <- case M.lookup k ov of
    Nothing -> randomRIO (lo, hi)
    Just v -> randomRIO (max lo $ v-1, min hi $ v+1)
  return $ M.insert k v' ov
  
pick m = do
  i <- randomRIO (0, M.size m - 1)
  return $ M.elemAt i m

-- option descriptions, each with admissible range of values 
type OD = M.Map Text (Int,Int)

od0 :: OD
od0 = M.fromList
  [ ("chrono",(0,1))
  , ("phase", (0,1))
  , ("quiet", (1,1))
  , ("seed", (0,0))
  , ("shrink", (0,3))
  , ("stable", (0,2))
  , ("target", (0,2))
  , ("tier1", (1, 100))
  , ("walkinitially", (0,1))
  ]

-- option values
type OV = M.Map Text Int

ov1 = M.fromList
  [ ("chrono",1),("quiet",1),("shrink",3),("stable",2),("target",1),("tier1",12)
  ]

ov0 = M.fromList [("quiet", 1),("phase",0)]

data Run = Run { ov :: OV
               , val :: NominalDiffTime
               } deriving Show

solveWithKissat
  :: Codec a
  => OV -> StateT SAT IO a -> IO (Result , Maybe (Decoded a))
solveWithKissat ov m =
  solveWith (kissatapi_with $ map (uncurry Option) $ M.toList ov) m

run
  :: OV
  -> (OV -> IO r)
  -> IO (Run, r)
run ov action = do
  begin <- getCurrentTime
  r <- action ov
  end <- getCurrentTime
  return (Run ov $ diffUTCTime end begin, r)




mainf :: Int -> Int -> IO (Maybe [[[[Bool]]]])
mainf d m = mainfor ov0 d m

mainfor ov dim muls = do
  out <- solveWithKissat ov $ do
    let mat = replicateM dim $ replicateM dim $ exists @Bit
    abcs <- replicateM muls $ replicateM 3 mat
    when False $ assert $ and (zipWith (<?) abcs $ tail abcs) 
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
      return $ Just abcs
    _ -> return Nothing

-- arguments: dim = 2, muls = 7
-- with  foldr1: 55 sec
-- with bfoldr1: 52 sec
-- most of that time is spent for proving unsolvability for muls=6
xors = bfoldr1 xor

bfoldr1 op xs =
  let go [x] = x
      go (x:y:zs) = go (zs <> [op x y])
  in  go xs

srow i m = show $ map fromEnum $ m !! i
