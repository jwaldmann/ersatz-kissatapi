{-# language FlexibleContexts #-}

module Ersatz.Solver.Kissat.API where

import Control.Monad.IO.Class

import qualified Data.IntSet as S
import qualified Data.IntMap as M

import Ersatz
import Control.Lens 
import qualified Kissat.API as API
import Control.Applicative ((<$>))

import Control.Monad (forM)
import Data.Foldable (forM_)

import System.IO
import Control.Exception (bracket, finally, mask_, onException )
import Control.Concurrent.Async

kissatapi :: MonadIO m => Solver SAT m
kissatapi problem = do
  let a = problem ^. lastAtom
      lit = API.MkLit . fromIntegral
  liftIO $ API.withNewSolverAsync $ \ solver -> do
    API.setOption solver "quiet" 1
    API.setConfiguration solver "sat"
    let cls = dimacsClauses problem

    let v = maximum $ map abs $ concatMap S.toList cls
        c = length cls
    hPutStrLn stderr $ unwords
      [ "CNF", show v, "vars", show c , "clauses"]
    
    forM_ cls $ \clause -> do
      API.addClause solver $ map lit $ S.toList clause
    ret <- API.solve solver
    if ret then do
      result <- M.fromList <$> ( forM [1..v] $ \ v -> do
          b <- API.getValue solver $ lit v
          return (v,b) )
      return (Satisfied , result)
    else
      return (Unsatisfied, M.empty)
