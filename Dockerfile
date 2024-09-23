####################################################################################################
# Stage 1: building Agda
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
# Stage 2: Download HoTT-Agda
####################################################################################################

FROM alpine AS hottagda

RUN apk add --no-cache git

COPY ["HoTT-Agda", "/dist/Hott-Agda"]
RUN echo "/dist/Hott-Agda/hott-core.agda-lib" > /dist/libraries

###############################################################################################################

FROM alpine

COPY --from=agda /dist /dist
COPY --from=hottagda /dist /dist

COPY ["Colimit-code", "/build/Colimit-code"]

WORKDIR /build/Colimit-code
RUN /dist/agda --library-file=/dist/libraries ./R-L-R/CosColimitEquiv2.agda
RUN /dist/agda --library-file=/dist/libraries ./R-L-R/CosColimitEquiv2Cont.agda
RUN /dist/agda --library-file=/dist/libraries ./R-L-R/CosColimitEquiv2Cont2.agda
RUN /dist/agda --library-file=/dist/libraries ./R-L-R/CosColimitEquiv2Cont3.agda
RUN /dist/agda --library-file=/dist/libraries ./R-L-R/CosColimitEquiv2Cont4.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CosColimit.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CosColimit2.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CosColimit3.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CosColimit4.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CosColimit5.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CosColimit6.agda
RUN /dist/agda --library-file=/dist/libraries ./L-R-L/CosColimit7.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap2.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap3.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap4.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap5.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap6.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap7.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap8.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap9.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap10.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap11.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap12.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap13.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap14.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap15.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap16.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap17.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap18.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap19.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap20.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap21.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap22.agda
RUN /dist/agda --library-file=/dist/libraries ./Map-Nat/CosColimitMap23.agda
RUN /dist/agda --library-file=/dist/libraries ./Main-theorem/CosColim-Adjunction.agda

CMD ["/dist/agda", "--html", "--library-file=/dist/libraries", "./Main-theorem/CosColim-Adjunction.agda"]