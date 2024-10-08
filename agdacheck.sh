#!/bin/sh

cd /build/Colimit-code
/dist/agda --html --library-file=/dist/libraries /build/Colimit-code/Main-Theorem/CosColim-Adjunction.agda

cd /build/Pullback-stability
/dist/agda --html --library-file=/dist/libraries /build/Pullback-stability/Stability.agda

