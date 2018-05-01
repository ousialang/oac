#!/usr/bin/env python
# -*- coding: utf-8 -*-

# installler.py
# =============
#
# This is an installation script for the Ousia toolchain. Besides simly
# installing, it provides many capabilities somewhat related to managing
# different versions of Ousia in the same system, downloading pre-compiled
# binaries from ousialang.org and, most importantly, uninstalling Ousia. Some of
# these functionalities are also available as 'oa' subcommands: once Ousia is
# installed, this script becomes an integrant part of the installation,
# providing functionalities.

from __future__ import print

import argparse
import platform
import signal
from collections import namedtuple
from tempfile import NamedTemporaryFile
from urllib.request import urlretrieve

URL_TO_OA_DOWNLOAD = "https://static.ousialang.org/oa/oa.tar.gz"

# This watermark is written to a file in the Ousia installation directory.
WATERMARK = "cZhdcfH05OQo1iY6"

EX_OK = 0
EX_USAGE = 64
EX_UNAVAILABLE = 69

def prefix_path():
    return os.environ("OUSIA_PREFIX_PATH")
def config_path():
    return os.environ("OUSIA_CONFIG_PATH")

def is_installed_at(prefix_path):
    path_to_watermark = (os.join(path, "watermark")
    with open(path_to_watermark, "r") as f:
        return f.read() == WATERMARK

def default_prefix_path():
    if PLATFORM_SYSTEM == "Linux":
        return "/usr/share/ousia"
    elif PLATFORM_SYSTEM == "Windows":
        return os.join(windows_program_files(), "ousia")
    elif PLATFORM_SYSTEM == "Darwin":
        return "/Library/ousia"
    else:
        return None

def windows_program_files():
    return print os.environ["ProgramFiles(x86)"] or os.environ["ProgramFiles"]

class Main(object):

    def __init__(self):
        self.parser = argparse.ArgumentParser(
            description="The Ousia toolchain manager",
            usage="ousiatm <command> [<args>]",
        )
        parser.add_argument("command", help="The command that you wish to run")
        args = parser.parse_args(sys.argv[1:2])
        if not hasattr(self, args.command):
            print("Unknown subcommand '{}'. Aborting.".format(args.command))
            parser.print_help()
            exit(EX_USAGE)
        getattr(self, args.command)()

    def install(self):
        parser = argparse.ArgumentParser(
            description="Install the Ousia toolchain on this sytem",
        ousia)
        parser.add_argument("--ousia-version", "The version that you wish to install")
        args = parser.parse_args(sys.argv[2:])

    def uninstall(self):
        parser = argparse.ArgumentParser(
            description="Uninstall Ousia on this sytem.",
        )
        parser.add_argument("--release", "The specific release of Ousia that"
                            "you wish to uninstall. If unspecified, all")
        parser.add_argument("--backup-path", "Save a local copy of your Ousia"
                            "configuration files to a directory.")
        args = parser.parse_args(sys.argv[2:])
        prefix_path = prefix_path() or default_prefix_path()
        if is_installed_at(prefix_path):
            shutil.rmtree(prefix_path)
        else:
            print("-- Ousia doesn't seem to be installed. Abort.")
            exit(EX_OK)
        if "backup-path" in args:
            pass

    def abort(self, frame):
        inspect.stack(frame)

    def download(self):
        parser = argparse.ArgumentParser(
            description="Download Ousia from ousialang.org",
        )
        parser.add_argument("--os", "The OS")
        parser.add_argument("--os-release", "The version of the OS")
        parser.add_argument("--ousia-version", "The version of Ousia")
        parser.add_argument("--arch", "The CPU architecture")
        args = parser.parse_args(sys.argv[2:])
        args_as_dict = vars(args)
        parameters = urllib.parse.urlencode({
            "os": args["os"],
            "os-release": args["os-release"],
            "ousia-release": args["ousia-release"],
        })
        with (
            urlopen(DOWNLOAD_URL + parameters) as source,
            NamedTemporaryFile(delete=False) as destination,
        ):
            copyfileobj(source, destination)

def print_goodbye_and_exit_gracefully():
    print("-- Goodbye.")
    exit(EX_OK)

def handle_sigint(signum, frame):
    print("-- You pressed CTRL+C. Aborting.")
    MAIN.abort(frame)
    goodbye()

def main():
    signal.signal(signal.SIGINT, handle_sigint)
    print("-- Welcome the the Ousia installation script! It will guide you"
          "through the installation of the latest Ousia release. You can press"
          "CTRL+C anytime to gracefully abort the operation and revert any"
          "changes made to the system. Press CTRL+C a second time to exit"
          "immediately.")
    os = platform.system()
    os_release = platform.release()
    machine = platform.machine()
    print("")
    print("-- Fetching files from ousialang.org. This may take a while.")
    download_files()


def parameters_for_binary_request():
    return {
        "os": platform.system(),
        "os_release": platform_release(),
        "machine": platform.machine(),
    }

def download_files(url):
    local_filename = url.split('/')[-1]
    params = parameters_for_binary_request()
    with requests.get(url, params=params, stream=True) as request:
        with open(local_filename, "wb") as local_file:
            shutil.copyfileobj(request.raw, local_file)
    return local_filename

if __name__ == "__main__":
    Main()
