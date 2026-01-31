#!/bin/sh

cd /build/Colimit-coslice
/dist/agda --html --library-file=/dist/libraries /build/Colimit-coslice/Main-Theorem/CosColim-main.agda
/dist/agda --html --library-file=/dist/libraries /build/Colimit-coslice/Create/Tree-preserve.agda
/dist/agda --html --library-file=/dist/libraries /build/Colimit-coslice/Create/Tree-reflect.agda
/dist/agda --html --library-file=/dist/libraries /build/Colimit-coslice/OFS-Preserve/CosColim-lftclass.agda
/dist/agda --html --library-file=/dist/libraries /build/Colimit-coslice/Coproduct/CosWedge.agda

cd /build/HoTT-Agda
/dist/agda --html --library-file=/dist/libraries /build/HoTT-Agda/theorems/homotopy/ColimAdjoint-hex.agda
/dist/agda --html --library-file=/dist/libraries /build/HoTT-Agda/theorems/homotopy/Acyc-colim.agda
/dist/agda --html --library-file=/dist/libraries /build/HoTT-Agda/theorems/modality/Mod-colim.agda

