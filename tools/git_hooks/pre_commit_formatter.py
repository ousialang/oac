#!/usr/bin/env python
# -*- coding: utf-8 -*-

# This pre-commit hook automatically formats source code files using tools like
# YAPF and clang-format. Any thrown error is considered a bug. It's fine if a
# formatting tool is not installed: it's much better to let the user commit
# their changes and deal with potentially bad formatted source files later.

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
    import jsbeautifier as jsb
    JSB = True
except ImportError:
    JSB = False

PYTHON_33 = sys.version_info >= (3, 3)
EXTENSIONS_CXX = (".c", ".h", ".cpp", ".cc", ".hpp")
EXTENSIONS_PY = (".py", )
EXTENSIONS_WEB = (".html", ".css", ".js")
EXTENSIONS_RUST = (".rs", )
EXTENSIONS = EXTENSIONS_CXX + EXTENSIONS_PY + EXTENSIONS_WEB + EXTENSIONS_RUST
NEEDS_FORMATTING = lambda x: x.endswith(EXTENSIONS)
HERE = os.path.realpath(__file__)
PROJECT_DIR = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
CLANG_FORMAT = "clang-format"
RUST_FMT = "rustfmt"


def print_formatting_notice(file_name):
    print("Formatting {}...".format(file_name))


def print_formatting_success(file_name):
    print("Formatting {} -- SUCCESS".format(file_name))


def print_formatting_fail(file_name):
    print("Formatting {} -- FAILED".format(file_name))


def format_cxx(file_name):
    # shutil.which is only available in Python 3.3+
    if PYTHON_33 and shutil.which(CLANG_FORMAT) is not None or not PYTHON_33:
        print_formatting_notice(file_name)
        try:
            subprocess.call([CLANG_FORMAT, "-i", file_name])
            print_formatting_success(file_name)
            return True
        except (subprocess.CalledProcessError, OSError) as e:
            print_formatting_fail(file_name)
            return False


def format_python(file_name):
    if YAPF:
        print_formatting_notice(file_name)
        FormatFile(file_name, in_place=True)
        print_formatting_success(file_name)
    return YAPF


def format_web(file_name):
    if JSB:
        print_formatting_notice(file_name)
        jsb.beautify_file(file_name)
        print_formatting_success(file_name)
    return JSB


def format_rust(file_name):
    if PYTHON_33 and shutil.which(RUST_FMT) is not None or not PYTHON_33:
        print_formatting_notice(file_name)
        try:
            subprocess.call([RUST_FMT,file_name])
            print_formatting_success(file_name)
            return True
        except (subprocess.CalledProcessError, OSError) as e:
            print_formatting_fail(file_name)
            return False


def format_sources(file_names):
    modified_file_names = []
    for file_name in file_names:
        if file_name.endswith(EXTENSIONS_CXX):
            success = format_cxx(file_name)
        elif file_name.endswith(EXTENSIONS_PY):
            success = format_python(file_name)
        elif file_name.endswith(EXTENSIONS_WEB):
            success = format_web(file_name)
        elif file_name.endswith(EXTENSIONS_RUST):
            sucess = format_rust(file_name)
        if success:
            modified_file_names.append(file_name)
    return modified_file_names


def git_add_file_names(file_names):
    subprocess.check_output(
        ["git", "add"] + file_names, stderr=subprocess.STDOUT)


def git_status_file_names():
    git_status_argv = [
        "git", "diff", "--name-only", "--cached", "--diff-filter=drc",
        "--no-renames"
    ]
    try:
        git_status = subprocess.check_output(
            git_status_argv, stderr=subprocess.STDOUT)
    except (subprocess.CalledProcessError, OSError) as e:
        return []
    lines = git_status.decode("utf-8").splitlines()
    return [os.path.join(PROJECT_DIR, l) for l in lines]


if __name__ == "__main__":
    file_names = [x for x in git_status_file_names() if NEEDS_FORMATTING(x)]
    git_add_file_names(format_sources(file_names))
    sys.exit(0)
