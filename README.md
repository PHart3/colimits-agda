## Overview

  This Agda code accompanies the following written materials:
  - the CSL 2025 paper [Coslice Colimits in Homotopy Type Theory](https://doi.org/10.4230/LIPIcs.CSL.2025.46)
  - the associated [arXiv article](https://doi.org/10.48550/arXiv.2411.15103)
  - the preprint
    [On Left Adjoints Preserving Colimits in HoTT](https://phart3.github.io/2coher-preprint.pdf)
    (accepted to CSL 2026)
  
  It has been checked with Agda 2.6.3 and 2.6.4.3.

## Organization

- `HoTT-Agda/`

  A stripped-down version of Andrew Swan's [HoTT-Agda](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) branch,
  with many additions and local changes for general lemmas used in our development of colimits and wild adjunctions.

  In particular, it includes wild category theory, centered on (co)limits and adjunctions satisfying 2-coherence properties. 
  We prove that such 2-coherent left adjoints preserve colimits (over graphs). Moreover, we prove that the suspension functor 
  is a 2-coherent left adjoint to Loop-space, for which we develop some new properties of homogeneous types. As a result, we get 
  a formal proof that suspension preserves colimits. We also prove that modalities, viewed as functors on coslices of Type, are 
  2-coherent left adjoints, hence preserve colimits. Another notable result is that an adjunction satisfying a practical hexagon 
  identity between the proofs of naturality in each varaible respects, in a precise sense, orthogonal factorization systems.
  We show that the colimit functor on Type-valued diagrams satisfies this hexagon identity.

  See `HoTT-Agda/README.md`
  for details and for the license of the work inside this
  directory.

- `Colimit-coslice/`

  The formalization of our pushout construction of coslice
  colimits as well as a couple of applications:
    - the fact that the forgetful functor creates tree-indexed colimits
	- the coslice colimit functor preserves the left class of an OFS on Type.

  See `Colimit-coslice/README.md` for details and for the
  license of the work inside this directory.

- `Pullback-stability/`

  Our formalization of pullback stability (or universality)
  for all ordinary colimits as well as the construction
  of the coslice cocone that induces the pullback stability
  map in the coslice category of types.

  See `Pullback-stability/README.md`
  for details and for the license of the work inside this
  directory.

## Type-checking with Docker

We have successfully tested the following Docker container on Linux but not on other operating systems.

1. Build Docker image:

   ```bash
   docker build . -t colimit
   ```

   The build installs Agda 2.6.4.3 and type checks our whole development.
   The entire build may take over an hour. The type checking of all our
   Agda code takes about 40 minutes on our host Ubuntu with 16 GB of RAM.
   (We see a 17% speed-up by using the `--save-metas` option.)
   
   **Note:** Check just the final two files in the Dockerfile for the
   theorems in the paper "On Left Adjoints Preserving Colimits in HoTT."

2. Generate HTML files:

   ```bash
   mkdir -p ./html1 ./html2
   docker run --mount type=bind,source=./html1,target=/build/Colimit-coslice/html \
     --mount type=bind,source=./html2,target=/build/HoTT-Agda/html \
     colimit
   ```

   The HTML files will be under `html1/` and `html2/`.

## Acknowledgement

  This material is based upon work supported by the Air Force Office of Scientific Research under award number FA9550-21-1-0009.
  Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not
  necessarily reflect the views of the United States Air Force.
  
