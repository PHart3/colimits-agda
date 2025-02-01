####################################################################################################
# Build Agda
####################################################################################################

ARG GHC_VERSION=9.4.7
FROM fossa/haskell-static-alpine:ghc-${GHC_VERSION} AS agda

WORKDIR /build/agda
# Agda 2.6.4.3
ARG AGDA_VERSION=714c7d2c76c5ffda3180e95c28669259f0dc5b5c
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
  cabal v2-install alex happy-2.0.2 && \
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

WORKDIR /build/HoTT-Agda
RUN /dist/agda --library-file=/dist/libraries ./theorems/homotopy/SuspAdjointLoop.agda

WORKDIR /build/Colimit-code
RUN /dist/agda --library-file=/dist/libraries ./Trunc-Cos/TruncAdj.agda
RUN /dist/agda --library-file=/dist/libraries ./Main-Theorem/CosColim-Adjunction.agda

WORKDIR /build/Pullback-stability
RUN /dist/agda --library-file=/dist/libraries ./Stability.agda

####################################################################################################
# Execute shell script to create html files for colimit code
####################################################################################################

WORKDIR /build
RUN ["chmod", "+x", "/agda-html.sh"]

CMD ["sh", "/agda-html.sh"]
