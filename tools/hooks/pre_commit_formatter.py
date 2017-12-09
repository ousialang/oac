#!/usr/bin/env python3

import os
import subprocess
import sys
from yapf.yapflib.yapf_api import FormatFile


def format_sources():
    git_status = subprocess.check_output(
        ["git", "status", "--porcelain", "-uno"], stderr=subprocess.STDOUT)
    git_status_lines = [
        file_name[3:] for file_name in git_status.decode("utf-8").splitlines()
    ]
    print("Running code formatters...")
    for file_name in git_status_lines:
        if file_name.endswith((".c", ".h", ".cpp", ".cc", ".hpp")):
            subprocess.call(["clang-format", "-i", file_name[3:]])
        elif file_name.endswith(".py"):
            FormatFile(file_name, in_place=True)
        subprocess.call(["git", "add", file_name])


if __name__ == "__main__":
    format_sources()
    sys.exit(0)
