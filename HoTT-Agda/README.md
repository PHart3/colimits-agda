Homotopy Type Theory in Agda
============================

This directory contains a heavily stripped-down version of Andrew Swan's [branch](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) of the
HoTT-Agda library. It also contains a bunch of additional lemmas, which arose during our
development of coslice colimits. The structure of the source code is described below.

Setup
-----

The library is compatible with Agda 2.6.3. To use it, you need a recent version of Agda and to include at
least the path to `hott-core.agda-lib` in your Agda library list.

Agda Options
------------

Each Agda file should have `--without-K --rewriting` in its header.
`--without-K` is for restricting pattern matching so that the uniqueness of identity proofs is not admissible.
`--rewriting` is for the computational rules of the higher inductive types.

Structure of the source
-----------------------

### Core library (directory `core/lib/`)

The main library is more or less divided into two parts.

- The first part is exported in the module `lib.Basics` and contains everything needed to make the second
  part compile
- The second part is found in `lib.types` and develops type formers.

Note that our work on colimits makes extensive use of the `path-seq/` directory.

Citation
--------

We copy here the citation for the original HoTT-Agda library.

```
@online{hott-in:agda,
  author={Guillaume Brunerie
    and Kuen-Bang {Hou (Favonia)}
    and Evan Cavallo
    and Tim Baumann
    and Eric Finster
    and Jesper Cockx
    and Christian Sattler
    and Chris Jeris
    and Michael Shulman
    and others},
  title={Homotopy Type Theory in {A}gda},
  url={https://github.com/HoTT/HoTT-Agda}
}
```

Names are roughly sorted by the amount of contributed code, with the founder Guillaume always staying on the
top.

License
-------
This work is released under [MIT license](https://opensource.org/licenses/MIT).
See [LICENSE.md](LICENSE.md).

Acknowledgments
---------------

This material was sponsored by the National Science Foundation under grant numbers CCF-1116703 and DMS-1638352;
Air Force Office of Scientific Research under grant numbers FA-95501210370 and FA-95501510053.
The views and conclusions contained in this document are those of the author and should not be
interpreted as representing the official policies, either expressed or implied, of any sponsoring
institution, the U.S. government or any other entity.