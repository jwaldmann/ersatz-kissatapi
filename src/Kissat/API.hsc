-- reference:
-- https://github.com/niklasso/minisat-haskell-bindings/blob/3280a2d88a67359265888a567e5d18f7ff49076a/MiniSat.hsc

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Kissat.API where

import Foreign.Ptr     ( Ptr, nullPtr )
import Foreign.C.Types ( CInt(..) )
import Control.Exception (bracket, finally, mask_, onException )
import Control.Concurrent.Async
import Control.Monad (forM_)

#include "kissat.h"
#include "hsc-magic.h"

#define CTYPE_solver kissat*
#define HTYPE_solver Solver
#define CTYPE_bool int
#define HTYPE_bool Bool
#define CTYPE_int int
#define HTYPE_int Int
#define CTYPE_lit int
#define HTYPE_lit Lit
#define CTYPE_var int
#define HTYPE_var Var

newtype Solver = MkSolver (Ptr ())
newtype Var    = MkVar CInt  deriving ( Eq, Ord, Num )
newtype Lit    = MkLit CInt  deriving ( Eq, Ord, Num )

-- semantics of IPASIR interface:
-- https://github.com/biotomas/ipasir/blob/master/ipasir.h

-- for Kissat:
-- Default (partial) IPASIR interface.

-- const char *kissat_signature (void);

-- kissat *kissat_init (void);
#unsafe kissat_init, 0, io(solver)

-- void kissat_add (kissat * solver, int lit);
#unsafe kissat_add, 2(solver, lit), io(unit)

-- int kissat_solve (kissat * solver);
-- 
#safe kissat_solve, 1(solver), io(int)

-- int kissat_value (kissat * solver, int lit);
#unsafe kissat_value, 2(solver, lit), io(lit)
  
-- void kissat_release (kissat * solver);
#unsafe kissat_release, 1(solver), io(unit)

-- void kissat_set_terminate (kissat * solver, void *state, int (*terminate) (void *state));

-- Additional API functions.

-- void kissat_terminate (kissat * solver);
#safe kissat_terminate, 1(solver), io(unit)

-- void kissat_reserve (kissat * solver, int max_var);

-- | Run a kissat instance in such a way that it is
-- interruptable (by sending killThread).
-- cf. https://github.com/niklasso/minisat-haskell-bindings/issues/1
withNewSolverAsync :: (Solver -> IO a) -> IO a
withNewSolverAsync h = 
  bracket newSolver deleteSolver $ \  s -> do
    mask_ $ withAsync (h s) $ \ a -> do
      wait a `onException` kissat_terminate s

withNewSolver :: (Solver -> IO a) -> IO a
withNewSolver h =
  do s <- newSolver
     h s `finally` deleteSolver s

newSolver = kissat_init
deleteSolver = kissat_release

addClause :: Solver -> [Lit] -> IO ()
addClause s xs = do
  forM_ xs $ kissat_add s
  kissat_add s 0

-- | returns True for SAT, False for UNSAT
solve :: Solver -> IO Bool
solve s = kissat_solve s >>= \ case
  10 -> return True
  20 -> return False
  
getValue :: Solver -> Lit -> IO Bool
getValue s l = do
  v <- kissat_value s l
  return $ if v == l then True
    else if v == negate l then False
    else if v == 0 then False
    else error "huh"
