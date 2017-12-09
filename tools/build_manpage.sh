#!/bin/sh

cd $(dirname $0)
cd ..
asciidoctor -b manpage -d manpage --out-file "build/man.1" "docs/man.adoc"
