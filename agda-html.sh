#!/bin/sh

cd /build/Colimit-code
/dist/agda --html --library-file=/dist/libraries /build/Colimit-code/Main-Theorem/CosColim-main.agda
/dist/agda --html --library-file=/dist/libraries /build/Colimit-code/Create/Tree-preserve.agda
/dist/agda --html --library-file=/dist/libraries /build/Colimit-code/Create/Tree-reflect.agda

