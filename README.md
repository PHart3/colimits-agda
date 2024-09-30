# Overview

  This Agda code accompanies our paper [Colimits in Homotopy Type Theory](https://phart3.github.io/colimits-paper.pdf).
  (The link points to the preprint.) It has been checked with Agda 2.6.3.

# Organization

- `HoTT-Agda/`

  A stripped down version of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda/),
  with local changes for general lemmas we proved during the development.

- `Colimit-code/`

  Our formalization of our construction of an A-colimit.
  See `Colimit-code/README.md` for details and for the
  license of the work inside this directory.

# Type-checking with Docker

1. Build Docker image:

   ```bash
   docker build . -t colimit
   ```

   The building itself type checks the whole development. The type-checking
   is partitioned into multiple stages, for otherwise the type-checking
   could take an unacceptably long time. The entire build may take over an hour.
   The type checking of `Colimit-code/` takes about 36 minutes on our host Ubuntu.

2. Generate HTML files:

   ```bash
   mkdir -p ./html
   docker run --mount type=bind,source=./html,target=/build/Colimit-code/html colimit
   ```

   The HTML files will be under `html/` and `html/CosColim-Adjunction.html`
   will be the entry point.

# Acknowledgement

  This material is based upon work supported by the Air Force Office of Scientific Research under award number FA9550-21-1-0009.
  Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not
  necessarily reflect the views of the United States Air Force.
  