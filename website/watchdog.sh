#!/usr/bin/env bash
cd $(dirname $0)
FLASK_APP=src/index.py python3 -m flask run & sass --watch scss:css
