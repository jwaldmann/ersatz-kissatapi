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
import Control.Monad (replicateM, forM_, when, join)
import Text.Printf
import System.IO
import System.Environment
import Data.Time.Clock
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Data.Text (Text)
import Control.Monad.State (StateT)
import System.Random
import Control.Timeout
import Control.Concurrent.Async
import System.IO
import GHC.Conc

main :: IO ()
main = do
  p <- getNumCapabilities
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering
  getArgs >>= \ case
    [] -> down 2 Nothing
    [d] -> down (read d) Nothing
    [d, m] -> down (read d) (Just $ read m)
    ["multi", d, m] -> multi_down p (read d) (Just $ read m)
    [ "walk", d, m ] ->
      walk_from p od0 ov1 $ \ ov -> mainfor ov (read d) ( read m)

down :: Int -> Maybe Int -> IO ()
down dim mmuls = do
  let go muls = mainf dim muls >>= \ case
        Nothing -> printf "no solution for dim = %d, mmuls = %d\n" dim muls
        Just _ -> go (muls - 1)
  hSetBuffering stdout LineBuffering
  go $ maybe (dim^3 ) id mmuls

multi_down :: Int -> Int -> Maybe Int -> IO ()
multi_down p dim mmuls = do
  let go ov muls = multi_mainf p ov dim muls >>= \ case
        Nothing -> printf "no solution for dim = %d, mmuls = %d\n" dim muls
        Just (o2, _) -> go o2 (muls - 1)
  hSetBuffering stdout LineBuffering
  go ov0 $ maybe (dim^3 ) id mmuls

walk_from :: Int -> OD -> OV -> (OV -> IO r) -> IO ()
walk_from p od ov0 action = do
  let work c ov =  do
          o2 <- changes c od ov
          run o2 action
  Just r0 <- bestof Nothing p $ work 1 ov0
  let go r1 = do
        mr <- bestofi (Just $ val r1) p $ \ i -> work i (ov r1)
        case mr of
          Just (r2, _) -> do
            printf "best %s, this %s\n" (show r1) (show r2)
            go r2
          _ -> do
            printf "keep best %s\n" (show r1) 
            go r1
  go $ fst r0

bestof mto k action = bestofi mto k $ \ i -> action

bestofi mto k action = do
  as <- mapM async $ flip map (take k  [0..])  $ \ i -> 
    ( case mto of
      Nothing -> (Just <$>)
      Just to -> timeout (2 * to)
      ) $ action i
  snd <$> waitAnyCancel as

changes 0 od ov = return ov
changes c od ov = change od ov >>= \ ov' -> changes (c-1) od ov'

change od ov = do
  (k,bnd@(lo,hi)) <- pick od
  v' <- case M.lookup k ov of
    Nothing -> randomRIO (lo, hi)
    Just v -> randomRIO  (max lo $ v-1, min hi $ v+1)
  return $ M.insert k v' ov
  
pick m = do
  i <- randomRIO (0, M.size m - 1)
  return $ M.elemAt i m

-- option descriptions, each with admissible range of values 
type OD = M.Map Text (Int,Int)

od0 :: OD
od0 = let bool = (0,1) in M.fromList
  [ ("backbone", (0,2))
  , ("bump", bool)
  , ("bumpreasons", bool)
  , ("chrono",bool)
  , ("definitions", bool)
  , ("eliminate", bool)
  , ("equivalences", bool)
  , ("extract", bool)
  , ("forcephase", bool)
  , ("forward", bool)
  , ("ifthenelse", bool)
  , ("minimize", bool)
  , ("otfs", bool)
  , ("phase", bool)
  , ("phasesaving", bool)
  , ("probe", bool)
  , ("promote", bool)
--  , ("quiet", (1,1))
  , ("reduce", bool)
  , ("reluctant", bool)
  , ("rephase", bool)
  , ("restart", bool)
  , ("seed", (0,0))
  , ("shrink", bool)
  , ("simplify", bool)
  , ("stable", (0,2))
  , ("substitute", bool)
  , ("sweep", bool)
  , ("target", (0,2))
  , ("tier1", (1, 100))
  , ("tier2", (1, 1000))
  , ("tumble", bool)
  , ("vivify", bool)
  , ("walkinitially", bool)
  , ("warmup", bool)
  ]

-- option values
type OV = M.Map Text Int

ov0 = ov2

ov1 = M.fromList
  [ ("chrono",1)
  ,("quiet",1)
  ,("shrink",3),("stable",2),("target",1),("tier1",12)
  ]

ov2 = M.fromList
  [("backbone",1),("bump",1),("bumpreasons",0),("chrono",1),("definitions",1)
  ,("eliminate",0),("equivalences",0),("extract",0),("forcephase",0)
  ,("forward",1),("ifthenelse",0),("minimize",1),("otfs",1),("phase",1)
  ,("phasesaving",1),("probe",0),("promote",1),("quiet",1),("reduce",1)
  ,("reluctant",1),("rephase",1),("restart",1),("seed",0),("shrink",1)
  ,("simplify",0),("stable",1),("substitute",0),("sweep",0),("target",0)
  ,("tier1",31),("tier2",976),("tumble",0),("vivify",1),("walkinitially",0)
  ,("warmup",1)
  ]

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

multi_mainf :: Int -> OV -> Int -> Int -> IO (Maybe (OV,Maybe [[[[Bool]]]]))
multi_mainf p ov d m = do
  hPutStrLn stderr
    $ printf "p = %d, ov = %s, d = %d, m = %d\n" p (show ov) d m
  bestofi Nothing p $ \ i -> do
    o2 <- changes i od0 ov
    r <- mainfor o2 d m
    hPutStrLn stdout $
      printf "input config %s\nsuccess for %s\ndiff %s\n"
        (show ov) (show o2) (show $ symdiff ov o2)
    return (o2, r)

symdiff :: (Ord k, Eq v) => M.Map k v -> M.Map k v -> M.Map k (Maybe v, Maybe v)
symdiff = M.merge
  (M.mapMissing $ \ k x -> (Just x, Nothing))
  (M.mapMissing $ \ k x -> (Nothing, Just x))
  (M.zipWithMaybeMatched $ \ k x y ->
      if x == y then Nothing else Just (Just x, Just y))

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
