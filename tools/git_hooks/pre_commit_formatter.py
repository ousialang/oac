#!/usr/bin/env python
# -*- coding: utf-8 -*-

# This pre-commit hook automatically formats source code files using tools like
# YAPF and clang-format. Any thrown error is considered a bug. It's fine if a
# formatting tool is not installed: it's much better to let the user commit
# their changes and deal with potentially bad formatted source files later.

from __future__ import with_statement

import os
import shutil
import subprocess
import sys

try:
    from yapf.yapflib.yapf_api import FormatFile
    YAPF = True
except ImportError:
    YAPF = False

try:
    from BeautifulSoup import BeautifulSoup as bsoup
    BSOUP = True
except ImportError:
    BSOUP = False

PYTHON_33 = sys.version_info >= (3, 3)
EXTENSIONS_CXX = (".c", ".h", ".cpp", ".cc", ".hpp")
EXTENSIONS_HTML = (".html", )
EXTENSIONS_PY = (".py", )
EXTENSIONS_RUST = (".rs", )
EXTENSIONS = EXTENSIONS_CXX + EXTENSIONS_HTML + EXTENSIONS_PY + EXTENSIONS_RUST
HERE = os.path.realpath(__file__)
PROJECT_DIR = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
CLANG_FORMAT = "clang-format"
RUST_FMT = "rustfmt"


def needs_formatting(file_name):
    return file_name.endswith(EXTENSIONS)


def print_formatting_notice(file_name):
    print("Formatting {}...".format(file_name))


def print_formatting_success(file_name):
    print("Formatting {} -- SUCCESS".format(file_name))


def print_formatting_fail(file_name):
    print("Formatting {} -- FAILED".format(file_name))


def print_formatting_fatal():
    print("Ousia's source formatter failed unexpectetly. Abort.")


def format_cxx(file_name):
    print_formatting_notice(file_name)
    try:
        subprocess.call([CLANG_FORMAT, "-i", file_name])
    except:
        print_formatting_fail(file_name)
        return False
    print_formatting_success(file_name)
    return True


def format_html(file_name):
    print_formatting_notice(file_name)
    try:
        with open(filename, "r+") as f:
            pretty_html = bsoup(f.read(), "html.parser").prettify()
            f.truncate(0)
            f.write(pretty_html)
    except:
        print_formatting_fail(file_name)
        return False
    print_formatting_success(file_name)
    return True


def format_python(file_name):
    print_formatting_notice(file_name)
    try:
        FormatFile(file_name, in_place=True)
    except:
        print_formatting_fail(file_name)
        return False
    print_formatting_success(file_name)
    return YAPF


def format_rust(file_name):
    print_formatting_notice(file_name)
    try:
        subprocess.call([RUST_FMT, file_name])
    except:
        print_formatting_fail(file_name)
        return False
    print_formatting_success(file_name)
    return True


def format_sources(file_names):
    modified_file_names = []
    for file_name in file_names:
        if file_name.endswith(EXTENSIONS_CXX):
            success = format_cxx(file_name)
        elif file_name.endswith(EXTENSIONS_HTML):
            success = format_html(file_name)
        elif file_name.endswith(EXTENSIONS_PY):
            success = format_python(file_name)
        elif file_name.endswith(EXTENSIONS_RUST):
            sucess = format_rust(file_name)
        if success:
            modified_file_names.append(file_name)
    return modified_file_names


def git_add_file_names(file_names):
    return subprocess.check_output(
        ["git", "add"] + file_names, stderr=subprocess.STDOUT)


def git_status_file_names():
    git_status_argv = [
        "git", "diff", "--name-only", "--cached", "--diff-filter=drc",
        "--no-renames"
    ]
    git_status = subprocess.check_output(
        git_status_argv, stderr=subprocess.STDOUT)
    lines = git_status.decode("utf-8").splitlines()
    return [os.path.join(PROJECT_DIR, l) for l in lines]


if __name__ == "__main__":
    try:
        file_names = [
            x for x in git_status_file_names() if needs_formatting(x)
        ]
        git_add_file_names(format_sources(file_names))
    except subprocess.CalledProcessError as e:
        print_formatting_fatal()
        sys.exit(e.returncode)
