#!/usr/bin/env bash

# HOW TO RUN:
#   $ cd oa/website
#   $ sh watchdog.sh

FLASK_APP=index.py python3 -m flask run & sass --watch assets/scss:static/css
