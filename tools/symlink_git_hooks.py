#!/usr/bin/env python
# -*- coding: utf-8 -*-
import os

if __name__ == "__main__":
    here = os.path.realpath(
        os.path.join(os.getcwd(), os.path.dirname(__file__)))
    hook_destination = os.path.join(
        os.path.dirname(here), ".git", "hooks", "pre-commit")
    hook_location = os.path.join(here, "git_hooks", "pre_commit_formatter.py")
    try:
        os.remove(hook_destination)
    except (FileNotFoundError, OSError) as e:
        pass
    # FIXME: possible race condition
    os.symlink(hook_location, hook_destination)
