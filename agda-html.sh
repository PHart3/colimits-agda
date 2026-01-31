#!/bin/sh

cd /build/Colimit-code
/dist/agda --html --library-file=/dist/libraries /build/Colimit-code/Main-Theorem/CosColim-main.agda
/dist/agda --html --library-file=/dist/libraries /build/Colimit-code/Create/Tree-preserve.agda
/dist/agda --html --library-file=/dist/libraries /build/Colimit-code/Create/Tree-reflect.agda
/dist/agda --html --library-file=/dist/libraries /build/Colimit-code/OFS-Preserve/CosColim-lftclass.agda

cd /build/HoTT-Agda
/dist/agda --html --library-file=/dist/libraries /build/HoTT-Agda/theorems/homotopy/Acyc-colim.agda
/dist/agda --html --library-file=/dist/libraries /build/HoTT-Agda/theorems/modality/Mod-colim.agda

