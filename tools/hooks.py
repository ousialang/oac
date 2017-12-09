#!/usr/bin/env/python
import os

if __name__ == "__main__":
  location = os.path.realpath(os.path.join(
    os.getcwd(),
    os.path.dirname(__file__)))
  git_location = os.path.join(
      os.path.dirname(location),
      ".git",
      "hooks",
      "git-clang-format.py")
  os.symlink(os.path.join(location, "hooks", "git-clang-format.py"),
             git_location)
