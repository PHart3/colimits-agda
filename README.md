## Overview

  This Agda code accompanies our paper [Coslice Colimits in Homotopy Type Theory](https://phart3.github.io/colimits-paper.pdf).
  (The link points to the preprint.) It has been checked with Agda 2.6.3.

## Organization

- `HoTT-Agda/`

  A stripped down version of Andrew Swan's [HoTT-Agda](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) branch,
  with local changes for general lemmas we proved during the development. It also includes a proof of the 2-coherence of
  the Suspension-Loop adjunction and some properties of homogenous types (used for the proof of 2-coherence).

  See HoTT-Agda/LICENSE.md for the license of the work inside this directory.

- `Colimit-code/`

  Our formalization of our construction of an A-colimit.

  See `Colimit-code/README.md` for details and for the
  license of the work inside this directory.

- `Pullback-stability/`

  Our formalization of pullback stability (or universality)
  for all ordinary colimits.

  See `Pullback-stability/README.md`
  for details and for the license of the work inside this
  directory.

## Type-checking with Docker

NOTE: We have successfully tested the following Docker container on Linux but not on other operating systems.

1. Build Docker image:

   ```bash
   docker build . -t colimit
   ```

   The building itself type checks the whole development. The type-checking
   is partitioned into multiple stages, for otherwise the type-checking
   could take an unacceptably long time. The entire build may take over an hour.
   The type checking of all our Agda code takes about 31 minutes on our host Ubuntu.

2. Generate HTML files:

   ```bash
   mkdir -p ./html1 ./html2
   docker run --mount type=bind,source=./html1,target=/build/Colimit-code/html \
     --mount type=bind,source=./html2,target=/build/Pullback-stability/html \
     colimit
   ```

   The HTML files will be under `html1/` and `html2/`.
   The entry points will be
   - `html1/CosColim-Adjunction.html`
   - `html2/Stability.html`

## Acknowledgement

  This material is based upon work supported by the Air Force Office of Scientific Research under award number FA9550-21-1-0009.
  Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not
  necessarily reflect the views of the United States Air Force.
  