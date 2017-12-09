#!/usr/bin/env/python3
import os

if __name__ == "__main__":
  location = os.path.realpath(os.path.join(
    os.getcwd(),
    os.path.dirname(__file__)))
  git_location = os.path.join(
      os.path.dirname(location),
      ".git",
      "hooks",
      "pre-commit")
  os.symlink(os.path.join(location, "hooks", "pre_commit_formatter.py"),
             git_location)
