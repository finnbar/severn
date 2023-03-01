# loop-compile

This is the code associated with the paper _This is Driving Me Loopy: Transforming loop in Arrowized Functional Reactive Programs_.

You can run the tests with `stack test` to see that a program behaves the same on random inputs pre- and post-transformation.
You can also run our benchmarks with `stack bench`.

Here is a quick overview of the files, which may be useful if you're looking through the code.
This is roughly in dependency order.

* `src/CFSF.hs` contains the definition of `CFSF`, alongside some helper functions like `isId` and `isDecoupled`. There are also a few useful typeclass instances.
* `src/ArrowCFSF.hs` provides a set of arrow combinators for `CFSF`. Note that due to their types differing from Haskell's `Arrow` typeclasses, `CFSF` is not a member of that typeclass.
* `src/Transform.hs` contains the transformation algorithm. Each operation in the paper corresponds to a function in this file.
* `src/Optimise.hs` contains our tiny optimisation pass, which merges composed `arr` terms.
* `src/Run.hs` contains functions for running a `CFSF` strictly. It is partial as it is undefined on `Loop`, but is defined for `LoopD` and `LoopM` so will work on any output of our transformation algorithm.
* `src/SFRP.hs` contains our implementation of SFRP, which is missing much of the optimisations of the original SFRP project.
* `src/Scratchpad.hs` contains a few example `CFSF`s, which you may find useful if you experiment with this library on the REPL.
* `gen/ArbitraryProgram.hs` contains our arbitrary program generation code.

The remaining files in `gen`, and all files in `test` and `benchmark`, are for the tests and benchmarks.