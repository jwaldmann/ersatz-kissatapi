-- | compute oscillator for Conway's game of life, 
-- cf. http://www.conwaylife.com/wiki/Category:Oscillators
-- example usage: ./dist/build/Life/Life 3 7
-- arguments are: period, width, height, number of live start cells
-- (or: cells in the rotor? TODO: introduce propert options parser)

{- nice example: 

.  .  .  .  .  .  .  .  .  .  .  . 
.  .  .  .  .  O  O  .  .  .  .  . 
.  .  .  .  .  O  O  .  .  .  .  . 
.  .  .  .  .  .  .  .  .  .  .  . 
.  .  .  O  O  O  O  O  O  .  .  . 
.  .  O  .  .  *  *  .  .  O  .  . 
.  O  .  O  *  *  *  X  O  .  O  . 
.  .  O  .  .  *  *  .  .  O  .  . 
.  .  .  O  O  O  O  O  O  .  .  . 
.  .  .  .  .  .  .  .  .  .  .  . 
.  .  .  .  .  O  O  .  .  .  .  . 
.  .  .  .  .  O  O  .  .  .  .  . 

period 8, box (12,12), rotor: 8, stator: 28

(this is known as R2D2)

-}


{-# language PatternSignatures #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language TupleSections #-}
{-# language DataKinds #-}
{-# language TypeFamilies #-}
{-# language DefaultSignatures #-}

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
import GHC.TypeNats
import Text.Printf
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import System.Environment


import Control.Monad ( guard, when, forM, foldM, void )
import System.Environment
import Data.Ix ( range, inRange )
import qualified Data.Map.Strict as M
import System.IO

data Config =
  Config { period :: Int
         , dim :: (Int,Int)
         , rotor_dim :: Maybe (Int,Int)
         , rotor_size :: Maybe Int
         , total_size :: Maybe Int
         } deriving (Show, Read)



main :: IO ()
main = void $ do
    argv <- getArgs
    case  map read argv of
        []             -> osc $ Config 3 (7,8) Nothing (Just 3) Nothing
        [ p, w, ww ] ->
          osc $ Config p (w,w) (Just (ww,ww)) Nothing Nothing
        [ p, w, ww, hh ] ->
          osc $ Config p (w,w) (Just (ww,hh)) Nothing Nothing
{-        
        [ p, w       ] -> osc $ Config p (w,w) Nothing Nothing  Nothing
        [ p, w, h    ] -> osc $ Config p (w,h) Nothing Nothing  Nothing
        [ p, w, h, r ] -> osc $ Config p (w,h) Nothing (Just r) Nothing
        [ p, w, h, r,s ] -> osc $ Config p (w,h) Nothing (Just r) (Just s)
-}

test = osc $ Config 3 (8,8) (Just (2,2)) Nothing  Nothing

count a = length $ filter id $ A.elems a

printA
  :: S.Set (Int,Int) 
  -> A.Array (Int,Int) Bool
  -> IO ()
printA rotor g = putStrLn $ unlines $ do
         let ((u,l),(o,r)) = A.bounds g
         x <- [u .. o]
         return $ unwords $ do 
             y <- [ l ..r ]
             let i = (x,y)
             return $ case (S.member i rotor , g A.!i) of
                  (False, False) -> ". "
                  (False,  True) -> "O "
                  (True,  False) -> "* "
                  (True,   True) -> "X "

instance (A.Ix a, A.Ix b) => Equatable (R.Relation a b) where
  r === s = encode (R.bounds r == R.bounds s)
    && R.elems r === R.elems s

instance (A.Ix a, A.Ix b) => Orderable (R.Relation a b) where
  r <? s = encode (R.bounds r == R.bounds s)
    && R.elems r <? R.elems s

osc
  :: Config
  -> IO ()
osc conf = do
  (status, Just gs) <-
      solveWith (kissatapi_with [ Configuration "sat"
                                -- , Option "quiet" 1
                                , Option "phase" 0
                                , Option "forcephase" 1
                                ]
                ) $ con conf
  case status of
    Satisfied -> do
      let m = M.fromListWith (<>) $ do
            g <- gs                  
            (i,x) <- A.assocs g
            return (i,S.singleton x)
          total =   length $ filter id $ A.elems $ gs !! 0 
          stator = M.keysSet $ M.filter (== S.singleton True) m
          rotor  = M.keysSet $ M.filter ((>1) . length) m
      forM ( zip [ 0..  ] gs ) $ \ (t, g) -> do
        putStrLn $ unwords [ "time", show t ]
        printA rotor g
      printf "period: %d, box: %s, total: %d, rotor: %d, stator: %d\n"
        (length gs-1) (show $ dim conf)
        total (length rotor) (length stator)
      hFlush stdout  
      osc $ conf { total_size = Just $ pred total }
    _ -> printf "done\n"

type Board = R.Relation Int Int

con :: MonadSAT s m
    => Config
    -> m [ Board ]
con c = do
  let (w,h) = dim c
      bnd = ((1,1), (w,h))

  gs <- case rotor_dim c of
    Nothing -> replicateM (period c + 1) $ R.relation bnd
    Just (rw,rh) -> do
      g0 <- R.relation bnd
      let (mw,mh) = (div (1+w) 2, div (1+h) 2)
          (u,d) =  (mw - div rw 2, mh - div rh 2)
          rbnd = ((u+1,d+1),(u+rw,d+rh))
      hs <- replicateM (period c + 1) $ R.relation rbnd    
      return $ map (with g0) hs
        
  assert $ all bordered gs
  
  assert $ head gs === last gs

  assert $ flip all (zip gs $ tail gs) $ \ (g,h) -> 
    flip all (R.assocs g) $ \ (pos, x) ->
      let n = sumBits $ neighbours g pos
      in  h R.! pos === (x && (encode 2 === n) || (encode 3 === n))
    
  assert $ case total_size c of
    Nothing -> true
    Just s -> C.atmost s $ R.elems $ head gs

  assert $ no_shorter_period (period c) bnd $ init gs

  return gs




equals_on p r s = and $ do
  i <- R.indices r
  guard $ p i
  return $ r R.! i === s R.! i

with r s = flip R.buildFrom (R.bounds r) $ \ i j ->
  let p = (i,j)
  in  (if A.inRange (R.bounds s) p then s else r) R.! p

inner ((u,l),(d,r)) =  ((u+1,l+1), (d-1,r-1))

border g =
  let bnd@((u,l),(d,r)) = R.bounds g
  in  flip R.buildFrom (R.bounds g) $ \ i j ->
        (g R.! (i,j))
        && encode (not $ A.inRange (inner bnd) (i,j))


isPrime n
  = all (\t -> 0 /= mod n t)
  $ takeWhile (\t -> t*t <= n) $ 2 : [3,5..]

prime_divisors n
  = filter (\p -> 0 == mod n p && isPrime p) [ 2 .. n ]

no_shorter_period p bnd gs =
  flip any (A.range bnd) $ \ pos ->
  flip all (prime_divisors p) $ \ t ->
  let d = div p t in
  flip any [0 .. length gs - 1 - d] $ \ i ->
  (gs!!i) R.! pos /== (gs!!(i+d)) R.! pos

next =
  -- next_field
  -- next_field_too
  -- next_simple step_unary
  next_simple step_spec

next_field_too p g =
  let ((u,l),(d,r)) = R.bounds g
      getf a i = if A.inRange (R.bounds a) i then a R.! i else false
      gr :: A.Array (Int,Int)
        -- N
        -- O
        (B.Binary 2)
        -- (U.Unary 4)
      gr = mka ((u-1,l),(d,r)) $ \ (i, j) ->
        C.fromBit (getf g (i,j)) + C.fromBit (getf g (i+1,j))
      gd = mka ((u,l-1),(d,r)) $ \ (i, j) ->
        C.fromBit (getf g (i,j)) + C.fromBit (getf g (i,j+1))
      getz a i = if A.inRange (A.bounds a) i
        then a A.! i else encode 0
  in  flip R.buildFrom (R.bounds g) $ \ i j ->
        let pos = (i,j)
            x = g R.! (i,j)
            a = (getz gr (i-1,j-1) + getz gd (i+1,j-1))
              + (getz gr (i+0,j+1) + getz gd (i-1,j+0))
            b = (getz gr (i+0,j-1) + getz gd (i-1,j-1))
              + (getz gr (i-1,j+1) + getz gd (i+1,j+0))
            n = if mod i 4 `elem` [0,1] then a else b
        in  if p pos then x && eqC 2 n || eqC 3 n else x

mka bnd f = A.array bnd $ map (\i -> (i, f i)) $ A.range bnd

next_field p g = 
  let fc :: [[ N ]]
      fc = field_count $ to_field g
      ((u,l),_) = R.bounds g
  in  R.build (R.bounds g) $ do
    (pos@(i,j),x) <- R.assocs g
    let c = fc !! (i-u) !! (j-l)
        v = eqC 3 c ||  (x && eqC 4 c)
    return (pos, if p pos then v else x)

-- | one-hot encoding:
-- number n is represented   by   xs!!n  being true.
newtype N = N [Bit] 

instance Num N where
  fromInteger 0 = N [true]
  N xs + N ys =
    N $ M.elems $ M.fromListWith (||) $ do
      (i,x) <- zip [0..] xs
      (j,y) <- zip [0..] ys
      return (i+j, x&&y)

instance C.FromBit N where
  fromBit b = N [not b, b]
    
instance Codec N where
  type Decoded N = Integer
  encode 0 = N [true]
  decode s (N xs) = do
    ys <- forM xs (decode s)
    return $ fromIntegral $ length $ takeWhile not ys

class (Codec n, Decoded n ~ Integer) => EqC n where
  eqC :: Integer -> n -> Bit
  default eqC :: Equatable n => Integer -> n -> Bit
  eqC k n = encode k === n

instance EqC N where
  eqC i (N xs) =
    let n = fromIntegral i
    in  if n < length xs then xs !! n else false

-- | order encoding:
-- number n is represented   by   xs!!k iff k <= n
newtype O = O [Bit] 

instance Num O where
  fromInteger 0 = O [true]
  O xs + O ys =
    O $ M.elems $ M.fromListWith (||) $ do
      (i,x) <- zip [0..] xs
      (j,y) <- zip [0..] ys
      return (i+j, x&&y)

instance C.FromBit O where
  fromBit b = O [true, b]
    
instance Codec O where
  type Decoded O = Integer
  encode 0 = O [true]
  decode s (O xs) = do
    ys <- forM xs (decode s)
    return $ fromIntegral $ pred $ length $ takeWhile id ys

instance EqC O where
  eqC n (O xs) =
    let w = length xs
        get j =
          let i = fromIntegral j
          in  if i < w then xs !! i else false
    in  get n && not (get $ n+1)

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

next_simple step p g = 
  R.build (R.bounds g) $ do
    (i,x) <- R.assocs g
    return (i, if p i then step x $ neighbours g i else x)

neighbours g (i,j) = do
            i' <- [ i-1, i, i+1 ]
            j' <- [ j-1, j, j+1 ]
            guard $ i /= i' || j /= j'
            guard $  A.inRange (R.bounds g) (i',j') 
            return $ g R.! (i', j')

-- | CNF 7756 vars 29693 clauses  37 sec
step_naive x xs =
  let n = sumBits xs in (x && n === encode 2) || (n === encode 3)
-- | CNF 6361 vars 35108 clauses   7 sec
step_unary x xs =
  let cs = census xs in (x && cs !! 2)        || cs !! 3
-- | CNF 11953 vars 54222 clauses  1min52
step_count x xs = x && C.exactly 2 xs || C.exactly 3 xs

step_spec x xs =
  let n ::
        B.Binary 2 -- CNF 6556 vars 26637 clauses  4 sec
        -- U.Unary -- 4 CNF 8362 vars 41631 clauses 20 sec
        -- O -- CNF 8107 vars 36988 clauses 9 sec
        -- N -- CNF 10609 vars 44726 clauses 28 sec
      n = sum $ map C.fromBit xs
  in  x && (eqC 2 n) || (eqC 3 n)

instance KnownNat w => EqC (B.Binary w)
instance KnownNat w => EqC (U.Unary w)


-- | census xs !! k <=> sumBits xs == k
census [] = [true]
census (x:xs) =
  let cs = census xs
  in  take 4
      $ zipWith (\ a b -> choose a b x)
        (cs <> [false]) ([false] <> cs)


