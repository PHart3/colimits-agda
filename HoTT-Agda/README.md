Homotopy Type Theory in Agda
============================

This directory contains a stripped-down version of Andrew Swan's [branch](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) of the HoTT-Agda 
library as well as a bunch of additional auxiliary lemmas, which arose during our 
development of coslice colimits. 

In addition, it contributes new machinery that is noteworthy in its own right:

- It contains a formal proof that wild adjunctions satisfying a higher hexagon identity
  preserve orthogonal factorization systems in a precise sense. It also verifies that
  the colimit-constant adjunction on Type satisfies this hexagon identity.
- It contains a formal proof that suspension is 2-coherent as a left adjoint to loop.
  We prove that suspension preserves graph-indexed colimits as a corollary. 
- It contains a formal proof of the 2-coherence of modality functors on coslices of 
  Type and, as a corollary, that they preserve graph-indexed colimits. As a consequence, 
  we formally derive the construction of such colimits in the full subcategory of modal 
  types.

The structure of the source code is described below.

Setup
-----

The library is compatible with Agda 2.6.3 and 2.6.4.
To use it, include `hott-core.agda-lib` and `hott-theorems.agda-lib` in your Agda libraries file (along with the latter's dependencies).

Agda Options
------------

Each Agda file should have `--without-K --rewriting` in its header.

`--without-K` is for restricting pattern matching so that the uniqueness of identity proofs is not admissible.
`--rewriting` is for the computational rules of the higher inductive types.

Moreover, files postulating HITs should have `--confluence-check` in their headers. This ensures that the
new rewriting rules keep the system confluent, so that type-checking remains at least semi-decidable.

Structure of the source
-----------------------

### Core library (directory `core/lib/`)

The main library is more or less divided into three parts.

- The first part is exported in the module `lib.Basics` and contains essential constructions.
- The second part is found in `lib.types` and develops type formers, including the inductive definition of colimits in
  Type (which we also call ordinary colimits).
  It also contains new facts about homogeneous types and reformulates some of the basic theory of the suspension type.
- The third part is found in `lib.wild-cats` and develops wild category theory.
  Here are some notable results found in this part:
	- A 2-coherent left adjoint between wild categories preserves colimiting cocones (`Ladj-colim.agda`).
	- Given univalent wild bicategories equipped with orthogonal factorization systems and 
	  a wild adjunction between them that satisfies a reasonable hexagon identity between the proofs of naturality in each 
	  varaible, if the right adjoint preserves the right class, then the left adjoint preserves the left class (`Adj-OFS-wc.agda`).
	- A lot of general theory about (co)cones.

### Homotopy (directory `theorems/homotopy/`)

This directory contains two proofs related to higher coherence conditions on wild categorical data:
- a proof that suspension is a 2-coherent left adjoint to loop
    - This higher coherence lets us prove that the suspension functor preserves	colimits. 
	As a corollary, we prove that pointed colimits preserve acyclic types via the 
	construction of coslice colimits from `../Colimit-code/`. Note that the proof of 
	2-coherence relies on our work on homogeneous types.
- a proof that the wild adjunction between colimit and the constant diagram functor on Type
  satisfies the hexagon condition and thus that colimit preserves the left class of an OFS on Type.

### Modality (directory `theorems/modality/`)

This directory contains a proof that for every modality M : Type -> Type, such as
truncation, the induced functor on coslices is a 2-coherent left adjoint. This property
lets us prove that M preserves colimits and construct colimits in the full subcategory of
modal types.

Citation
--------

The extension and modification of HoTT-Agda presented here is due to Perry Hart.

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

**If using the version of HoTT-Agda presented in this repo, please cite both the original authors and Perry Hart.**

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
