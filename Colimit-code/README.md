## Summary

This directory contains a formalization of our pushout construction
of an A-colimit. Specifically, it shows that it's the left adjoint
to the constant diagram functor by presenting the expected natural
isomorphism.

It also contains a proof of the corollary that the forgetful functor
creates (i.e., preserves and reflects) tree-indexed colimits.

## Organization

- The `Aux/` folder contains auxiliary definitions and lemmas,
  usually formulated in an ad-hoc manner.

- The `CosCoc/` folder contains the basic development of diagrams and cocones in coslices of Type.

- The `Cos-WC/` folder contains the definition of the wild coslice category of types.

- The `Cocone-PO/` folder contains the definition of the colimiting pushout together with its A-cocone structure.

  This pushout and its A-cocone structure are described in **Section 5.3** of the (CSL) paper.

- The two homotopies making up the equivalence in **Theorem 15**
  of the paper are in `L-R-L/` and `R-L-R/`.

  - The file `L-R-L/CC-Equiv-LRL-7.agda` contains the witness
    of the left inverse of `postcomp`.
  - The file `R-L-R/CC-Equiv-RLR-4.agda` contains the
    witness of the right inverse of `postcomp`.

- The `Map-Nat/` folder contains a proof that the equivalence of
  Theorem 15 is natural both in diagrams and in coslice objects.

  - The file `CosColimitMap00.agda` contains the definition
    of the action of our pushout construction on maps of diagrams.
    This action is defined in **Section 5.4** of the paper.

  - The file `CosColimitPstCmp.agda` contains the proof
    of **Lemma 16** of the paper. (The first naturality square, arising
    from post-composition with coslice maps.)

  - The file `CosColimitPreCmp.agda` contains the proof
    of **Lemma 17** of the paper. (The second naturality square,
    arising from pre-composition with diagram maps.)

- The `Main-Theorem/` folder gathers all data of the desired
  adjunction from `L-R-L/`, `R-L-R/`, and `Map-Nat/`.

- The `Create/` folder contains the proof of **Theorem 18** of the paper,
  which states that the forgetful functor creates all tree-indexed colimits.
  It uses `Cos-WC/`.

- The `Trunc-Cos` folder contains a stand-alone proof of the 2-coherence of
  the truncation functor on the wild coslice category of types.

## Naming of Individual Files

In `L-R-L/`, `R-L-R/`, and `Map-Nat/`, Agda files are artificially
broken into many fragments with numeric suffixes so that Agda can
manage the type checking.

## Manual Type-Checking

1. Install Agda 2.6.3 or 2.6.4.
2. Add `cos-colim.agda-lib` and `../HoTT-Agda/hott-core.agda-lib` to your Agda libraries file.
3. Type check the files
 - `Main-Theorem/CosColim-main.agda`
 - `Create/Tree-preserve.agda`
 - `Create/Tree-reflect.agda`

## License

This work is released under Mozilla Public License 2.0.
See [LICENSE.txt](LICENSE.txt).
