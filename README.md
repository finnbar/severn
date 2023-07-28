# Severn

This is the code associated with the paper _This is Driving Me Loopy: Efficient loops in Arrowized Functional Reactive Programs_. This repository holds a minimal implementation of Severn as of the release of the paper, and will only be updated for bugfixes. This repo is a cleaned-up version of a private repo, hence why the commit dates are all grouped together.

You can run the tests with `stack test` to see that a program behaves the same on random inputs pre- and post-transformation.
You can also run our benchmarks with `stack build loop-compile:bench:bench-vs-yampa`. Raw results can be found in `tests.csv` (for the fixed benchmarks) and `tests-random.csv` (for the random benchmarks). The spreadsheet `tests.xlsx` contains the results and speedup calculations.

Here is a quick overview of the files, which may be useful if you're looking through the code.
This is roughly in dependency order.

* `src/CFSF.hs` contains the definition of `CFSF`, alongside some helper functions like `isId` and `isDecoupled`. There are also a few useful typeclass instances.
* `src/ArrowCFSF.hs` provides a set of arrow combinators for `CFSF`. Note that due to their types differing from Haskell's `Arrow` typeclasses, `CFSF` is not a member of that typeclass.
* `src/Transform.hs` contains the transformation algorithm. Each operation in the paper corresponds to a function in this file.
* `src/Optimise.hs` contains our tiny optimisation pass, which merges composed `arr` terms.
* `src/Run.hs` contains functions for running a `CFSF` strictly. It is partial as it is undefined on `Loop`, but is defined for `LoopD` and `LoopM` so will work on any output of our transformation algorithm.
* `src/Scratchpad.hs` contains a few example `CFSF`s, which you may find useful if you experiment with this library on the REPL.
* `gen/ArbitraryProgram.hs` contains our arbitrary program generation code.

The remaining files in `gen`, and all files in `test` and `benchmark`, are for the tests and benchmarks.

If you would like to try out some example expressions in the REPL, run `stack repl`. `ArrowCFSF` provides the required arrow combinators for building small AFRP programs, and `Run` lets you run `CFSF`s strictly via `transformAndRun`. You may also want to use `Scratchpad` for some example `CFSF`s.

Note that `Val` are printed using a special Show instance: `Pair`s are printed as `[|x, y|]` and `One`s are just printed as the value they contain. `CFSF`s are also printed specially, as `Arr` are annotated with their arity - _e.g._ `Arr[P(V)(V)->V]` means that it takes a pair of values to a single one.