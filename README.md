NooBDD
======

A pure implementation of BDDs in Haskell.

Created for educational reasons, probably poor performance and many bugs.

We leave reduction and memory optimization to the Haskell Compiler.
The main data type is naive and simple:

    data Bdd = Top | Bot | Node Int Bdd Bdd
