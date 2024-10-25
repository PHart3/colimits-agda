####################################################################################################
# Build Agda
####################################################################################################

ARG GHC_VERSION=9.4.7
FROM fossa/haskell-static-alpine:ghc-${GHC_VERSION} AS agda

WORKDIR /build/agda
ARG AGDA_VERSION=b499d12412bac32ab1af9f470463ed9dc54f8907
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
# Type check Agda files
####################################################################################################

FROM alpine AS hottagda

COPY ["HoTT-Agda", "/build/Hott-Agda"]
COPY ["Colimit-code", "/build/Colimit-code"]

FROM alpine

COPY --from=agda /dist /dist
COPY --from=hottagda /build /build

COPY ["Pullback-stability", "/build/Pullback-stability"]
COPY agdacheck.sh /

RUN echo "/build/Hott-Agda/hott-core.agda-lib" >> /dist/libraries
RUN echo "/build/Colimit-code/cos-colim.agda-lib" >> /dist/libraries
RUN echo "/build/Pullback-stability/stab.agda-lib" >> /dist/libraries

WORKDIR /build/Colimit-code
RUN /dist/agda --library-file=/dist/libraries ./R-L-R/CC-Equiv-RLR-0.agda
RUN /dist/agda --library-file=/dist/libraries ./R-L-R/CC-Equiv-RLR-1.agda
RUN /dist/agda --library-file=/dist/libraries ./R-L-R/CC-Equiv-RLR-2.agda
RUN /dist/agda --library-file=/dist/libraries ./R-L-R/CC-Equiv-RLR-3.agda
RUN /dist/agda --library-file=/dist/libraries ./R-L-R/CC-Equiv-RLR-4.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CC-Equiv-LRL-0.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CC-Equiv-LRL-1.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CC-Equiv-LRL-2.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CC-Equiv-LRL-3.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CC-Equiv-LRL-4.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CC-Equiv-LRL-5.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CC-Equiv-LRL-6.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CC-Equiv-LRL-7.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap00.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap01.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap02.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap03.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap04.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap05.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap06.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap07.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap08.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap09.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap10.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap11.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap12.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap13.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap14.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap15.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap16.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap17.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap18.agda
RUN /dist/agda --library-file=/dist/libraries ./Main-Theorem/CosColim-Adjunction.agda

WORKDIR /build/Pullback-stability
RUN /dist/agda --library-file=/dist/libraries ./Stability.agda

####################################################################################################
# Execute shell script to create html files
####################################################################################################

WORKDIR /build
RUN ["chmod", "+x", "/agdacheck.sh"]

CMD ["sh", "/agdacheck.sh"]
