#!/usr/bin/env python
# -*- coding: utf-8 -*-

import platform
import requests
import signal

BINARY_URL = "https://static.ousialang.org/oa.tar.gz/latest"

def goodbye():
    print("-- Goodbye.")

def handle_sigint(signum, frame):
    print("-- You pressed CTRL+C. Aborting.")

def main():
    print("-- Welcome the the Ousia installation script! It will guide you"
          "through the installation of the latest Ousia release. You can press"
          "CTRL+C anytime to gracefully abort the operation and revert any"
          "changes made to the system. Press CTRL+C another time to immediately"
          "exit.")
    os = platform.system()
    os_release = platform.release()
    machine = platform.machine()
    print("")
    print("-- Fetching files. This may take a while.")
    download_file()


def parameters_for_binary_request():
    return {
        "os": platform.system(),
        "os_release": platform_release(),
        "machine": platform.machine(),
    }

def download_file(url):
    local_filename = url.split('/')[-1]
    params = parameters_for_binary_request()
    with requests.get(url, params=params, stream=True) as request:
        with open(local_filename, "wb") as local_file:
            shutil.copyfileobj(request.raw, local_file)
    return local_filename

if __name__ == "__main__":
    signal.signal(signal.SIGINT, handle_sigint)
    main()
