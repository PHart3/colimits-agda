# Summary

This directory contains a formalization of our pushout construction
of an A-colimit. Specifically, it shows that it's the left adjoint
to the constant diagram functor by presenting the expected natural
isomorphism.

# Organization

- The `Aux/` folder contains auxiliary definitions and lemmas,
  including the inductive definition of ordinary colimits and
  the basic development of coslices of Type.

  - The file `Aux/Cocone.agda` contains the definition of
    the colimiting pushout together with its A-cocone structure.
  - This pushout and its A-cocone structure are described
    in Section 5.3 of the paper.

- The two homotopies making up the equivalence in Theorem 12
  of the paper are in `L-R-L/` and `R-L-R/`.

  - The file `L-R-L/CC-Equiv-LRL-7.agda` contains the witness
    of the left inverse of `postcomp`.
  - The file `R-L-R/CC-Equiv-RLR-4.agda` contains the
    witness of the right inverse of `postcomp`.

- The `Map-Nat/` folder contains a proof that the equivalence of
  Theorem 12 is natural both in diagrams and in coslice objects.

  - The file `Map-Nat/CosColimitMap00.agda` contains the definition
    of the action of our pushout construction on maps of diagrams.
    This action is defined in Section 5.4 of our paper.

  - The file `Map-Nat/CosColimitPstCmp.agda` contains the proof
    of Lemma 13 of the paper. (The first naturality square, arising
    from post-composition with coslice maps.)

  - The file `Map-Nat/CosColimitPreCmp.agda` contains the proof
    of Lemma 14 of the paper. (The second naturality square,
    arising from pre-composition with diagram maps.)

- The `Main-Theorem/` folder gathers all data of the desired
  adjunction from `L-R-L/`, `R-L-R/`, and `Map-Nat/`.

# Naming of Individual Files

In `L-R-L/`, `R-L-R/`, and `Map-Nat/`, Agda files are artificially
broken into many fragments with numeric suffixes in order to type
check the entire development in a reasonable amount of time.

# Manual Type-Checking

1. Install Agda 2.6.3.
2. Install the stripped, modified HoTT-Agda under `../HoTT-Agda`.
3. Type check the file `Main-Theorem/CosColim-Adjunction.agda`.

# License

This work is released under Mozilla Public License 2.0.
See [LICENSE.txt](LICENSE.txt).
