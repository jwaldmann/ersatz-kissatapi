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
{-# language TypeApplications #-}
{-# language ScopedTypeVariables #-}
{-# language AllowAmbiguousTypes #-}
{-# language DefaultSignatures #-}

import Prelude hiding ((&&),(||),not, or, and,all,any )
import qualified Prelude
import qualified Data.Bool as DB
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
import System.Directory

import Control.Monad ( guard, when, forM, foldM, void )
import System.Environment
import Data.Ix ( range, inRange )
import qualified Data.Map.Strict as M
import System.IO
import System.FilePath
import Data.Hashable
import Options.Applicative
import Control.Concurrent.Async

data Config =
  Config { period :: Int
         , width :: Int
         , height :: Maybe Int
         , total_size :: Maybe Int
         , rotor_width :: Maybe Int
         , rotor_height :: Maybe Int
         , rotor_size :: Maybe Int
         , symmetries :: [Sym]
         , spec :: Maybe Spec
         , match_type :: Match_Type
	 , period_check :: Period_Check
         } deriving (Show, Read)

dim c = (width c, maybe  (width c) id $ height c)
rotor_dim c = case rotor_width c of
  Nothing -> Nothing
  Just w -> Just (w, maybe w id $ rotor_height c)

c0 = Config { period = 2
            , width = 5
            , height = Nothing
            , total_size = Just 20
            , rotor_width = Nothing
            , rotor_height = Nothing
            , rotor_size = Nothing
            , symmetries  = []
            , spec = Just BB
            , match_type = Flat
	    , period_check = Local
            }

pconfig :: Parser Config
pconfig = Config
  <$> option auto (long "period" <> short 'p' <> value (period c0) )
  <*> option auto (long "width"  <> short 'w' <> value (width c0) )
  <*> option (Just <$> auto)
      (long "height"  <> short 'h' <> value Nothing )
  <*> option (Just <$> auto)
      (long "size"  <> short 's' <> value Nothing )
  <*> option (Just <$> auto)
      (long "rotor-width"  <> short 'W' <> value Nothing )
  <*> option (Just <$> auto)
      (long "rotor-height"  <> short 'H' <> value Nothing )
  <*> option (Just <$> auto)
      (long "rotor-size"  <> short 'S' <> value Nothing )
  <*> option ( fmap (map (read . return)) str)
      (long "symmetries" <> short 'y' <> value [])
  <*> option (Just <$> auto)
      (long "spec"  <> short 'e' <> value Nothing)
  <*> pure Flat
  <*> (   flag' (Global All) (long "global-all" <> short 'a')
      <|> flag' (Global Div) (long "global-div" <> short 'd')
      <|> flag  Local (Local) (long "local" <> short 'l')
      )
  
opts = info (pconfig <**> helper)
      ( fullDesc  <> progDesc "find CGoL oscillator"   )
       

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering
  osc =<< execParser opts  


test = osc $ c0 

count a = length $ filter id $ A.elems a

printA
  :: S.Set (Int,Int) 
  -> A.Array (Int,Int) Bool
  -> [String]
printA rotor g = do
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


parallel_specs conf specs = do
  as <- forM specs $ \ sp -> async $ do
      fmap (sp,) $ solveWith (kissatapi_with [ Configuration "sat"
                                -- , Option "quiet" 1
                                , Option "phase" 0
                                , Option "forcephase" 1
                                ]
                ) $ con $ conf { spec = Just sp }
  (_, out) <- waitAnyCancel as
  return out

parallel_match_types conf mts = do
  as <- forM mts $ \ mt -> async $ do
      fmap (mt,) $ solveWith (kissatapi_with [ Configuration "sat"
                                -- , Option "quiet" 1
                                , Option "phase" 0
                                , Option "forcephase" 1
                                ]
                ) $ con $ conf { match_type = mt }
  (_, out) <- waitAnyCancel as
  return out


osc
  :: Config
  -> IO ()
osc conf = do
  (mt, (status, Just gs))
    <- parallel_specs conf spec_types
      -- parallel_match_types conf match_types
  case status of
    Satisfied -> do
      let m = M.fromListWith (<>) $ do
            g <- gs                  
            (i,x) <- A.assocs g
            return (i,S.singleton x)
          total =   length $ filter id $ A.elems $ gs !! 0 
          stator = M.keysSet $ M.filter (== S.singleton True) m
          rotor  = M.keysSet $ M.filter ((>1) . length) m
      let header =
            printf "period: %d, box: %s, total: %d, rotor: %d, stator: %d, sym: %s, type: %s\n"
            (length gs-1) (show $ dim conf)
            total (length rotor) (length stator)
            (concat $ map show $ symmetries conf) (show mt)
          info = unlines $ header : do
            (t,g) <- zip [ 0..  ] gs
            ( printf "time %s" (show t) : printA rotor g )
      let d = ("p" <> show (period conf))
             </> ("s" <> show total)
          fn = d </> (show $ hash $ map A.elems gs) <.> "text"
      createDirectoryIfMissing True d 
      writeFile fn info
      putStrLn info
      printf "written to %s\n" fn
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
      let fixed = not . A.inRange rbnd
      return $ map (with g0) hs

  forM_ (symmetries c) $ \ s -> do
    forM_ gs $ \ g -> do
      assert $ g === sym s g

  assert $ all bordered gs
  
  assert $ head gs === last gs

  forM_ (zip gs $ tail gs) $ \ (g,h) -> do
    assert $ h === case the $ spec c of
      BI -> next_field @Bits (const True) g 
      BB -> next_field @(B.Binary 3) (const True) g 
      UU -> next_field @(U.Unary 5) (const True) g
      NN -> next_field @N (const True) g
      OO -> next_field @O (const True) g

  {-
  case spec c of
    BI -> conform @Bits fixed gs
    BB -> conform @(B.Binary 2) fixed gs
    UU -> conform @(U.Unary 4) fixed gs
    NN -> conform @N fixed gs
    OO -> conform @O fixed gs
  -}  

  {-
  forM_ (A.range bnd) $ \ pos ->
    if fixed pos && all fixed (neighbours_pos bnd pos)
    then matches (match_type c) (head gs, head gs) pos
    else forM_ (zip gs $ tail gs) $ \ (g,h) -> 
       matches (match_type c) (g,h) pos
  -}

  assert $ case total_size c of
    Nothing -> true
    Just s -> C.atmost s $ R.elems $ head gs

  case rotor_size c of
    Nothing -> return ()
    Just s -> do
      let rbnd = ((1,1), maybe (dim c) id $ rotor_dim c)
      rot <- R.relation rbnd
      assert $ C.atmost s $ R.elems rot
      assert $ flip all (A.range rbnd) $ \ pos ->
        let xs = map (R.! pos) gs
            changes = not (and xs) && or xs
        in  changes ==> rot R.! pos

  assert $ no_shorter_period (period_check c) (period c)
    (A.range bnd) $ init gs

  return gs

the (Just s) = s


data Sym = C | H | V | D deriving (Eq, Ord, Show, Read, Enum,Bounded)

sym s g =
  let bnd@((u,l),(d,r)) = R.bounds g
  in  case s of
         C -> flip R.buildFrom bnd $ \ i j -> g R.! (u+d-i, l+r-j)
         H -> flip R.buildFrom bnd $ \ i j -> g R.! (i, l+r-j)
         V -> flip R.buildFrom bnd $ \ i j -> g R.! (u+d-i, j)
         D -> flip R.buildFrom bnd $ \ i j -> g R.! (j,i)

assert_block s xs = do
  up <- monotone (length xs)
  down <- reverse <$> monotone (length xs)
  let bimod = zipWith (&&) up down
  assert $ and $ zipWith (==>) xs bimod
  assert $ not $ or $ zipWith (&&) bimod $ drop s bimod

monotone k = do
  xs <- replicateM k exists
  assert $ and $ zipWith (==>) xs $ tail xs
  return xs

rows a = do
  let ((u,l),(d,r)) = R.bounds a
  x <- [u..d]
  return $ do
    y <- [l..r]
    return $ a R.! (x,y)

cols a = do
  let ((u,l),(d,r)) = R.bounds a
  y <- [l..r]
  return $ do
    x <- [u..d]
    return $ a R.! (x,y)



conform 
  :: forall t s m
  . (C.FromBit t, EqC t, Num t, MonadSAT s m)
  => ((Int,Int) -> Bool)
  -> [R.Relation Int Int] -> m ()
conform fixed gs = do
  let bnd = R.bounds $ head gs
      gees = map (gee @t) gs
  forM_ (A.range bnd) $ \ pos@(i,j) -> do
    let safe = all fixed $ pos : neighbours_pos bnd pos
        f = if safe then take 1 else id
    forM_ (f $ zip gees $ tail gees) $ \ (g,h) -> do
      let x = base g R.! pos; x' = base h R.! pos
          c =
            if even i == even j
            then (horz g A.!(i-1,j-1) + horz g A.!(i+1,j  ))
               + (vert g A.!(i  ,j-1) + vert g A.!(i-1,j+1))
            else (vert g A.!(i-1,j-1) + vert g A.!(i  ,j+1))
               + (horz g A.!(i-1,j  ) + horz g A.!(i+1,j-1))
      assert $ x' === (eqC 2 c && x || eqC 3 c)     


data Gee t = Gee
  { base :: R.Relation Int Int
  , horz :: A.Array (Int,Int) t
  , vert :: A.Array (Int,Int) t
  }

gee
  :: forall t
  . (C.FromBit t, Num t)
  => R.Relation Int Int -> Gee t
gee g =
  let n = afrom (R.bounds g) $ \ i -> C.fromBit (g R.! i)
  in  Gee g (hor n) (ver n)

-- hor g = h <=> h[x,y] = g[x,y]+g[x,y+1]
-- used for x == y (mod 2) only
hor g =
  let ((u,l),(d,r)) = A.bounds g
      bnd = ((u-1,l-1),(d+1,r+1)) 
  in  afrom bnd $ \ p@(x, y) ->
        let q = (x,y+1) in
        case (A.inRange(A.bounds g)p,A.inRange(A.bounds g) q) of
          (False,False) -> 0
          (False,True) -> g A.! q
          (True,False) -> g A.! p
          (True,True)  -> g A.! p + g A.! q

ver g =
  let ((u,l),(d,r)) = A.bounds g
      bnd = ((u-1,l-1),(d+1,r+1)) 
  in  afrom bnd $ \ p@(x, y) ->
        let q = (x+1,y) in
        case (A.inRange(A.bounds g)p,A.inRange(A.bounds g) q) of
          (False,False) -> 0
          (False,True) -> g A.! q
          (True,False) -> g A.! p
          (True,True)  -> g A.! p + g A.! q


afrom bnd f = A.array bnd $ map (\i -> (i, f i)) $ A.range bnd

data Match_Type = Onehot Hot | Flat | Atmo | Step Step
  deriving (Read, Show)

match_types = fmap Onehot hot_types
   <> [ Flat, Atmo ]
   <> fmap Step step_types

data Hot = Plain | Split 
  deriving (Read, Show, Bounded, Enum)

hot_types = [ minBound .. maxBound @Hot ]


matches (Onehot var) (g,h) pos = do
      let x = g R.! pos
          xs = neighbours g pos
          d = length xs
          x' = h R.! pos
      c <-
        (case var of { Plain -> count4; Split -> count4' }) xs
      let { cs = contents c }
      assert $ or [ not x',    not $ cs !! 0 ]
      assert $ or [ not x',    not $ cs !! 1 ]
      assert $ or [ not x', x, not $ cs !! 2 ]
      assert $ or [ x', not x, not $ cs !! 2 ]
      assert $ or [ x',        not $ cs !! 3 ]
      assert $ or [ not x',    not $ cs !! 4 ]

matches Flat (g,h) pos = do
      let x = g R.! pos
          xs = neighbours g pos
          d = length xs
          x' = h R.! pos
      forM_ (seqs 4 xs) $ \ ys ->
        assert $ or $ not x' : map not ys
      forM_ (seqs (d-1) xs) $ \ ys ->
        assert $ or $ not x' : ys
      forM_ (replicateM d [False,True]) $ \ bs -> do
        let form = zipWith ($) (map (DB.bool id not) bs) xs
        case length $ filter id bs of
          2 -> do
            assert $ or $ not x' :     x : form
            assert $ or $     x' : not x : form
          3 -> do
            assert $ or $     x' :         form
          _ -> return ()  
  
matches Atmo (g,h) pos = do
      let x = g R.! pos
          xs = neighbours g pos
          d = length xs
          x' = h R.! pos
      m1 <- atmost 1 xs
      assert $ or [ not x', not m1 ]
      let { l2 = not m1 } ; m2 <- atmost  2 xs
      assert $ or [ not x',     x, not l2, not m2 ]
      assert $ or [     x', not x, not l2, not m2 ]
      let { l3 = not m2 } ; m3 <- atmost  3 xs
      assert $ or [     x',        not l3, not m3 ]
      let { l4 = not m3 }
      assert $ or [ not x', not l4 ]

matches (Step s) (g,h) pos = do
      let x = g R.! pos
          xs = neighbours g pos
          d = length xs
          x' = h R.! pos
      assert $ x' === -- step_spec
                      step_unary
                      x xs             


-- | one-hot encoding for numbers 0, 1, 2, 3, >=4
newtype OH4 = OH4
  { contents :: [Bit] -- ^ length 5
  }

oh4 :: MonadSAT s m => m OH4
oh4 = do
  xs <- replicateM 5 exists
  assert $ or xs
  forM_ (seqs 2 xs) $ \ ys -> assert $ or $ map not xs
  return $ OH4 xs

count4' xs =
  if length xs <= 4 then count4 xs
  else do
    let (pre,post) = splitAt (div (length xs) 2) xs
    a <- count4' pre
    b <- count4' post
    plus a b

count4 :: MonadSAT s m => [Bit] -> m OH4
count4 xs = do
  c <- oh4
  forM_ (replicateM (length xs) [False,True]) $ \ bs -> do
     let n = min 4 $ length $ filter id bs
         form = zipWith ($) (map (DB.bool id not) bs) xs
     forM_ [0..4] $ \ k -> do
       let t = contents c !! k
       assert $ or $ (if k==n then t else not t) : form
  return c     

plus ::  MonadSAT s m => OH4 -> OH4 -> m OH4
plus a b = do
  c <- oh4
  forM_ (zip [0..] $ contents a) $ \ (i,x) ->
    forM_ (zip [0..] $ contents b) $ \ (j,y) -> do
      let n = min 4 $ i + j
      forM_ [0..4] $ \ k -> do
        let t = contents c !! k
        assert $ or $ [if k==n then t else not t, not x, not y ]
  return c      

seqs 0 _ = return []
seqs k [] = []
seqs k (x:xs) = seqs k xs <> fmap (x:) (seqs (k-1) xs)

atleast k xs = do
  e <- exists
  forM_ (seqs k xs) $ \ ys ->
    assert $ or $ e : map not ys
  forM_ (seqs (length xs - (k - 1)) xs) $ \ ys ->
    assert $ or $ not e : ys
  return e  
atmost k xs = atleast (length xs - k) $ map not xs

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

data Who = All | Div
  deriving (Read, Show)
data Period_Check = Global Who | Local
  deriving (Read, Show)

no_shorter_period pc = case pc of
  Global All -> no_shorter_period_A
  Global Div -> no_shorter_period_B
  Local -> no_shorter_period_C

-- | globally different (the picture as maximal period)
no_shorter_period_A p ps gs =
  flip all (init $ tail gs) $ \ h ->
  flip any ps $ \ pos ->
  head gs R.! pos /== h R.! pos

-- | globally different (the picture as maximal period)
no_shorter_period_B p ps gs =
  flip all (prime_divisors p) $ \ t ->
  let d = div p t in
  flip any ps $ \ pos ->
  (gs!!0) R.! pos /== (gs!!d) R.! pos

-- | there is a cell of maximal period
no_shorter_period_C p ps gs =
  flip any ps $ \ pos ->
  flip all (prime_divisors p) $ \ t ->
  let d = div p t in
  flip any [0 .. length gs - 1 - d] $ \ i ->
  (gs!!i) R.! pos /== (gs!!(i+d)) R.! pos



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

next_field
  :: forall t
  . (C.FromBit t, EqC t, Num t)
  => ((Int,Int) -> Bool)
  -> R.Relation Int Int
  -> R.Relation Int Int
next_field p g = 
  let fc :: [[ t ]]
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

neighbours g pos =
  map (g R.!) $ neighbours_pos (R.bounds g) pos

neighbours_pos bnd (i,j) = do
            i' <- [ i-1, i, i+1 ]
            j' <- [ j-1, j, j+1 ]
            guard $ i /= i' || j /= j'
            guard $  A.inRange bnd (i',j') 
            return (i', j')

data Step = Naive | Unary | Count | Spec Spec
  deriving (Read, Show)

step_types = [ Naive, Unary, Count ] <> fmap Spec spec_types

-- | CNF 7756 vars 29693 clauses  37 sec
step_naive x xs =
  let n = sumBits xs in (x && n === encode 2) || (n === encode 3)
-- | CNF 6361 vars 35108 clauses   7 sec
step_unary x xs =
  let cs = census xs in (x && cs !! 2)        || cs !! 3
-- | CNF 11953 vars 54222 clauses  1min52
step_count x xs = x && C.exactly 2 xs || C.exactly 3 xs

data Spec = BI | BB | UU | OO | NN
  deriving (Read, Show, Enum, Bounded)

spec_types = [minBound .. maxBound @Spec]

step_spec BB = step_spec_imp @(Bits)
step_spec BB = step_spec_imp @(B.Binary 2)
step_spec UU = step_spec_imp @(U.Unary 4)
step_spec NN = step_spec_imp @(N)
step_spec OO = step_spec_imp @(O)

step_spec_imp
  :: forall t
  . (C.FromBit t, EqC t, Num t)
  => Bit -> [Bit] -> Bit
step_spec_imp x xs = 
  let n :: t
        -- B.Binary 2 -- CNF 6556 vars 26637 clauses  4 sec
        -- U.Unary 4 -- CNF 8362 vars 41631 clauses 20 sec
        -- O -- CNF 8107 vars 36988 clauses 9 sec
        -- N -- CNF 10609 vars 44726 clauses 28 sec
      n = sum $ map C.fromBit xs
  in  x && (eqC 2 n) || (eqC 3 n)

instance KnownNat w => EqC (B.Binary w)
instance KnownNat w => EqC (U.Unary w)

instance C.FromBit Bits where  fromBit x = Bits [x]
instance EqC Bits

-- | census xs !! k <=> sumBits xs == k
census [] = [true]
census (x:xs) =
  let cs = census xs
  in  take 4
      $ zipWith (\ a b -> choose a b x)
        (cs <> [false]) ([false] <> cs)


