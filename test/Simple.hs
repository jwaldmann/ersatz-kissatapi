module Main where

import Kissat.API

main = do
  withNewSolverAsync $ \  s -> do
    addClause s [1]
    addClause s [-1]
    b <- solve s
    print b
