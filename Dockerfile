####################################################################################################
# Build Agda
####################################################################################################

ARG GHC_VERSION=9.4.7
FROM fossa/haskell-static-alpine:ghc-${GHC_VERSION} AS agda

WORKDIR /build/agda
# Agda 2.6.4
ARG AGDA_VERSION=f42acb696e43d382639f04f869e9a99ab36a91c6
RUN \
  git init && \
  git remote add origin https://github.com/agda/agda.git && \
  git fetch --depth 1 origin "${AGDA_VERSION}" && \
  git checkout FETCH_HEAD

# We build Agda and place it in /dist along with its data files.
# We explicitly use v1-install because v2-install does not support --datadir and --bindir
# to relocate executables and data files yet.
RUN \
  mkdir -p /dist && \
  cabal update && \
  cabal v1-install alex happy && \
  cabal v1-install --bindir=/dist --datadir=/dist --datasubdir=/dist/data --enable-executable-static

####################################################################################################
# Type-check Agda files
####################################################################################################

FROM alpine AS hottagda

COPY ["HoTT-Agda", "/build/HoTT-Agda"]
COPY ["Colimit-code", "/build/Colimit-code"]

FROM alpine

COPY --from=agda /dist /dist
COPY --from=hottagda /build /build

COPY ["Pullback-stability", "/build/Pullback-stability"]
COPY agda-html.sh /

RUN echo "/build/HoTT-Agda/hott-core.agda-lib" >> /dist/libraries
RUN echo "/build/HoTT-Agda/hott-theorems.agda-lib" >> /dist/libraries
RUN echo "/build/Colimit-code/cos-colim.agda-lib" >> /dist/libraries
RUN echo "/build/Pullback-stability/stab.agda-lib" >> /dist/libraries

WORKDIR /build/Colimit-code
RUN /dist/agda +RTS -M4.5G -RTS --library-file=/dist/libraries ./Main-Theorem/CosColim-main.agda
RUN /dist/agda --library-file=/dist/libraries ./Create/Tree-preserve.agda
RUN /dist/agda --library-file=/dist/libraries ./Create/Tree-reflect.agda

WORKDIR /build/Pullback-stability
RUN /dist/agda --library-file=/dist/libraries ./Stability-ord.agda
RUN /dist/agda --library-file=/dist/libraries ./Stability-cos-coc.agda

WORKDIR /build/HoTT-Agda
RUN /dist/agda --library-file=/dist/libraries ./theorems/homotopy/Susp-colim.agda
RUN /dist/agda --library-file=/dist/libraries ./theorems/modality/Mod-colim.agda

####################################################################################################
# Execute shell script to create html files
####################################################################################################

WORKDIR /build
RUN ["chmod", "+x", "/agda-html.sh"]

CMD ["sh", "/agda-html.sh"]
