#!/usr/bin/env bash

# HOW TO RUN:
#   $ cd oa/website
#   $ sh watchdog.sh

export FLASK_APP=index.py
export FLASK_DEBUG=1
python3 -m flask run #& sass --watch assets/scss:static/css
