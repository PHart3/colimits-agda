# Organization

- `HoTT-Agda/`

  A stripped down version of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda/),
  with local changes for general lemmas we proved during the development.

- `Colimit-code/`

  Our formalization of our construction of an A-colimit.
  See `Colimit-code/README.md` for more details.

# Type-Checking with Docker

1. Build Docker image (which takes more than one hour on our machines):

   ```bash
   docker build . -t colimit
   ```

   The building itself type checks the whole development. (The type-checking
   is partitioned into multiple stages, for otherwise the type-checking
   could take an unacceptably long time.)

2. Generate HTML files:

   ```bash
   mkdir -p ./html
   docker run --mount type=bind,source=./html,target=/build/Colimit-code/html colimit
   ```

   The HTML files will be under `html/` and `html/CosColim-Adjunction.html`
   will be the entry point.
   