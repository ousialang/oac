#!/usr/bin/env bash
cd $(dirname $0)
cd ..
asciidoctor -b manpage -d manpage --out-file "target/man.1" "docs/man.adoc"
