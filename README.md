## Overview

  This Agda code accompanies both our CSL 2025 paper [Coslice Colimits in Homotopy Type Theory](https://doi.org/10.4230/LIPIcs.CSL.2025.46)
  and our associated [arXiv article](https://doi.org/10.48550/arXiv.2411.15103).
  
  It has been checked with Agda 2.6.3 and 2.6.4.

## Organization

- `HoTT-Agda/`

  A stripped-down version of Andrew Swan's [HoTT-Agda](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) branch,
  with specific additions and local changes for general lemmas used in our development of colimits.

  In addition, it includes wild category theory, centered on (co)limits and 2-coherent left adjoints. We prove that such adjoints
  preserve colimits (over graphs). Moreover, we prove that the Suspension functor is a 2-coherent left adjoint to Loop-space, for
  which we develop some new properties of homogeneous types. As a result, we get a formal proof that Suspension preserves colimits.

  See `HoTT-Agda/README.md` for the license of the work inside this directory.

- `Colimit-code/`

  Our formalization of our construction of an A-colimit
  as well as the fact that the forgetful functor creates
  tree-indexed colimits.

  See `Colimit-code/README.md` for details and for the
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

   The build installs Agda 2.6.4 and type checks our whole development.
   The entire build may take over an hour. The type checking of all our
   Agda code takes about 40 minutes on our host Ubuntu with 16 GB of RAM.

2. Generate HTML files:

   ```bash
   mkdir -p ./html
   docker run --mount type=bind,source=./html,target=/build/Colimit-code/html colimit
   ```

   The HTML files will be under `html`.

## Acknowledgement

  This material is based upon work supported by the Air Force Office of Scientific Research under award number FA9550-21-1-0009.
  Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not
  necessarily reflect the views of the United States Air Force.
  