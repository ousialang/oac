#!/bin/sh

cd $(dirname $0)
cd ..
asciidoctor -b manpage -d manpage --out-file "build/ousia.1" "docs/ousia.adoc"
