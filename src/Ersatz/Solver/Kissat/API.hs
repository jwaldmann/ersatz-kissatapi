{-# language FlexibleContexts, LambdaCase #-}

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

data Setting
  = Configuration String
  | Option String Int deriving (Read, Show, Eq, Ord)

kissatapi :: MonadIO m => Solver SAT m
kissatapi = kissatapi_with [ Configuration "sat", Option "quiet" 1 ]
  
kissatapi_with settings problem = do
  let a = problem ^. lastAtom
      lit = API.MkLit . fromIntegral
  liftIO $ API.withNewSolverAsync $ \ solver -> do
    forM_ settings $ \ case
      Configuration name -> API.setConfiguration solver name
      Option name val ->   API.setOption solver name val

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
