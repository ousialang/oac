#!/usr/bin/env python
# -*- coding: utf-8 -*-

import errno
import os
import platform
import shutil
import sys

DIR_ZENZI = ""
DIR_PLUGINS = os.path.join(DIR_ZENZI, "plugins/")
DIR_BINARY = "TODO"
ZENZI_INSTALL_DIR_FOR_DARWIN = "/Library/zenzi/"
READ_FILE_PERMISSION_NUMBER = 292


def install_for_darwin():
    if DIR_ZENZI:
        os.mkdir(ZENZI_INSTALL_DIR_FOR_DARWIN)
    else:
        pass


def install_usage_txt(zenzi_dir):
    install_resource(zenzi_dir, "usage.txt")


def install_for_windows():
    pass


def install_for_linux():
    pass


def setup_dir(zenzi_dir):
    try:
        os.makedirs(os.path.join(zenzi_dir, "plugins/"))
    except OSError as e:
        if e.errno != errno.EEXIST:
            raise
    try:
        os.makedirs(os.path.join(zenzi_dir, "modules/"))
    except OSError as e:
        if e.errno != errno.EEXIST:
            raise
    VERSION_FILE_PATH = os.path.join(zenzi_dir, "version.txt")
    if not os.path.exists(VERSION_FILE_PATH):
        with open(VERSION_FILE_PATH, "a", "ascii") as file:
            file.write("{{{VERSION_MAJOR}}}."
                       "{{{VERSION_MINOR}}}."
                       "{{{VERSION_FIX}}}-"
                       "{{{VERSION_BUILD}}}")
        # TODO set read-only permissions for version file
    shutil.copyfile(ZENZI_EXECUTABLE, os.path.join(zenzi_dir, "ousia"))


def uninstall():
    pass  # TODO


if __name__ == "__main__":
    ZENZI_EXECUTABLE = sys.argv[1]
    PLATFORM_NAME = platform.system()
    PLATFORM_IS_DARWIN = PLATFORM_NAME == "Darwin"
    PLATFORM_IS_WINDOWS = PLATFORM_NAME == "Windows"
    PLATFORM_IS_LINUX = PLATFORM_NAME == "Linux"
    if PLATFORM_IS_DARWIN:
        ZENZI_DIR = "/Library/ousia/"
        EXECUTABLES_DIR = "/usr/bin/ousia"
    elif PLATFORM_IS_WINDOWS:
        ZENZI_DIR = os.environ["ProgramFiles"]
    elif PLATFORM_IS_LINUX:
        ZENZI_DIR = "/usr/share/ousia/"
        ZENZI_DIR = "/usr/bin/ousia"
    setup_dir(zenzi_DIR)
