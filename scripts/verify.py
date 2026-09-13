#!/usr/bin/env python3
# -*- coding: ascii -*-
"""Run the three stdlib censuses and the source guard."""
from __future__ import print_function

import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPTS = os.path.join(ROOT, "scripts")

CHECKS = [
    "census_span.py",
    "census_bits.py",
    "census_weights.py",
    "check_source.py",
]


def main():
    failed = 0
    for name in CHECKS:
        path = os.path.join(SCRIPTS, name)
        print("==== %s ====" % name)
        sys.stdout.flush()
        rc = subprocess.call([sys.executable, path], cwd=ROOT)
        if rc != 0:
            failed += 1
            print("FAILED %s (exit %s)" % (name, rc))
        print()
    if failed:
        print("VERIFY RED: %d script(s) failed" % failed)
        return 1
    print("VERIFY GREEN")
    return 0


if __name__ == "__main__":
    sys.exit(main())
