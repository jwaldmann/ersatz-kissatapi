-- | see Clausecker and Kaiser: Sliding Puzzles
-- Satcomp 2021 proceedings (p. 57)
-- https://helda.helsinki.fi/handle/10138/333647

-- cited there:  Korf and Felner:
-- Disjoint pattern database heuristics
-- https://doi.org/10.1016/S0004-3702(01)00092-3


{-# language LambdaCase, PatternSignatures, OverloadedStrings #-}

import Prelude hiding ((&&),(||),not, or, and, all, any )
import qualified Prelude
import Ersatz
import Ersatz.Solver.Kissat.API
import Control.Applicative
import Control.Monad
import Data.List ( tails, transpose )
import qualified Data.Ix as Ix
import qualified Data.Array as A
import System.Random.Stateful
import qualified Control.Monad.State.Strict as CMS
import System.Environment
import GHC.Word

type Nat = Word8
type Pos = (Nat,Nat)

data Swap = Swap Pos Pos deriving Show

swaps w = do
  let r = (0,w-1)
  x <- Ix.range r;  y <- Ix.range r
  swaps_from w (x,y)

swaps_from w (x,y) = do  
  let r = (0,w-1)
  dx  <-[ -1, 0, 1 ];  dy <- [ -1, 0, 1 ]
  guard $ (dx == 0) /= (dy == 0)
  let x' = x + dx ; y' = y + dy
  guard $ Ix.inRange r x' && Ix.inRange r y'
  return $ Swap (x,y) (x',y')

initial w =
  let r = ((0,0),(w-1,w-1))
  in  State (A.array r $ map (\ p -> (p,p)) $ A.range r) (0,0)


data State = State { table :: A.Array Pos Pos, blank :: Pos }
  deriving Show

apply s@(Swap p q) (State a b) | a A.! b == (0,0) =
  State (swap s a) q

swap (Swap p q) a = a A.// [(p, a A.! q), (q, a A.! p)]

make :: Nat -> Int -> Int -> (State, [Swap], State)
make w n  seed = runStateGen_ (mkStdGen seed) $ \ g -> do
  let go :: State -> Int -> CMS.State StdGen ([Swap], State)
      go s k =
        if k == 0
        then return ([], s)
        else do
          let ops = swaps_from w (blank s)
          i <- uniformRM (0, length ops - 1) g
          let op = ops !! i
              s' = apply op s
          (ops, final) <- go s' (k-1)
          return (op : ops, final)
  (ops, final) <- go (initial w) n
  return (initial w, ops, final)


-- | instance given in Korf/Felner (113 moves)
kf_data =
  [23,1,12,6,16
  ,2,20,10,21,18
  ,14,13,17,19,22
  ,0,15,24,3,7
  ,4,8,5,9,11
  ]
  
kf_inst =
  let pos i = divMod i 5
      r = (0, 4)
      f = A.listArray ((0,0),(4,4)) $ map pos kf_data
  in  (table $ initial 5, f)

  
-- | 5 by 5 grid: 2 bit is not enough for one co-ordinate
type PosEnc = (Bit3, Bit3)

instance (Ix.Ix i, Equatable a) => Equatable (A.Array i a) where
  a === b = encode ( A.bounds a == A.bounds b)
    && (A.elems a === A.elems b)

main = getArgs >>= \ case
  [ "kf" ] -> run 5 kf_inst 113
  [] -> run_random 5 10 314159
  [w, n, s] -> run_random (read w) (read n) (read s)
  _ -> error "arguments: side length of square, number of moves, seed for pseudo random gen"

run_random w steps seed = do
  let (initial, ops, final) = make w steps seed
  run w (table initial, table final) steps

run (w::Nat) (initial, final) steps = do

  let solver = kissatapi_with [ Configuration "sat"
                              , Option "walkinitially" 1
                              ]
  (Satisfied, Just as) <- solveWith solver $ do
    as :: [ A.Array Pos PosEnc ] <- replicateM (steps + 1)
      $ fmap (A.listArray ((0,0),(w-1,w-1)))
      $ replicateM (fromIntegral $ w^2)
      $ literally exists

    assert $ head as === encode initial
    assert $ last as === encode final

    assert $ flip all (zip as $ drop 1 as) $ \ (this, next) ->
      let eq = A.array (A.bounds this)
            $ flip map (A.indices this)
            $ \ i -> (i, this A.! i === next A.! i)
      in  flip any (swaps w) $ \ (op@(Swap from to)) ->
            (this A.! from === encode (0,0))
        --  &&  (next === swap op this)
        && flip all (A.indices this)
             ( \ i -> if i == from then this A.! i === next A.! to
                 else if i == to   then this A.! i === next A.! from
                 else eq A.! i
             )
        
    return as
  mapM_ (print . A.elems) as


