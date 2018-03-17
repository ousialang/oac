#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from flask import Flask
app = Flask(__name__)

from flask import render_template


@app.route("/")
def hello():
    return render_template("index.html")
