# Haskell API for Kissat SAT Solver

Kissat <http://fmv.jku.at/kissat/> is an award-winning
SAT solver by Armin Biere.
It already provides an IPASIR interface to C programs.

This package here adds a Haskell interface 
(modelled after <https://github.com/niklasso/minisat-haskell-bindings> by Niklas Sorenson), 
and a connector for the Ersatz <https://hackage.haskell.org/package/ersatz> library for SAT encoding 
(connector modelled after <https://github.com/jwaldmann/ersatz-minisatapi>).
