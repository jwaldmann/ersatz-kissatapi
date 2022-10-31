{-# language LambdaCase, TypeApplications #-}

import Prelude hiding ((||),(&&),not,and,or,all,any)
import Ersatz
import Ersatz.Solver.Kissat.API
import Control.Monad (replicateM)

main = do
  let rw = 5; w = 10
  let go h = do
        handle rw w h >>= \ case
          Nothing -> return ()
          Just t -> do
            mapM_ print $ map (map fromEnum) t
            print (rw, w, h)
            go $ succ h
  go 1

{-
          6    7    8   9  10  11  12

rw = 2   10   13   17  21  26  31  37
rw = 3   10   13   17  21  26  31  37
rw = 4   15   21   31  41  56
rw = 5   18   28   46  68  


0 (-> 1) -> c ; 0c -> 10; 1c -> c0

0^k -(2^k-1)-> 1^k

    0 0^k
->> 0 1^k -- Induktion
->  1 0^k -- (1 -> c hinten, 1c -> c0 bis vorn, dann 0c -> 10)
->> 1 1^k -- Induktion


0 = baa
1 = aba
c = aab

baa    -> aab
baaaab -> abaaab
abaaab -> aabbaa

-}

handle rw w h = do  
  out <- solveWith kissatapi $ do
    t <- replicateM h $ replicateM w $ exists @Bit
    assert
      $ flip all (zip t $ tail t) $ \ (u,v) ->
        flip any [0 .. w - rw]    $ \ k ->
          let (ul,umr) = splitAt k u
              (um,ur) = splitAt rw umr
              (vl,vmr) = splitAt k v
              (vm,vr) = splitAt rw vmr
          in  ul === vl
             && um >? vm
             && sumBits um === sumBits vm
             && ur === vr
    return t
  case out of
    (Satisfied, Just t) -> return $ Just t
    _ -> return Nothing

  
