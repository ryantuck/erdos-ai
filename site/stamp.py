#!/usr/bin/env python3
"""Content stamp for the corpus, so make can detect real changes safely.

Why this exists rather than listing the corpus as make prerequisites: the
pipeline rule `conjectures/%.lean : tidy/%.html` means any target depending on
a .lean file can make GNU make decide that file is out of date and "rebuild" it
— which runs an LLM formalization and overwrites reviewed work. Naming those
files as prerequisites is a footgun. So nothing does; instead this hashes the
inputs and rewrites the stamp file only when the hash actually changes, leaving
its mtime alone otherwise. Targets depend on the stamp.

    python3 site/stamp.py site/.corpus.stamp
"""

import hashlib
import glob
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PATTERNS = [
    "conjectures/*.lean",
    "conjectures-v2/*.lean",
    "conjectures-v2-haiku/*.lean",
    "fable-review/*.md",
    "haiku-review/*.md",
]


def digest():
    h = hashlib.sha256()
    for pattern in PATTERNS:
        for path in sorted(glob.glob(os.path.join(ROOT, pattern))):
            st = os.stat(path)
            h.update(os.path.relpath(path, ROOT).encode())
            h.update(str(st.st_size).encode())
            h.update(str(int(st.st_mtime)).encode())
    return h.hexdigest()


def main():
    target = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "site", ".corpus.stamp")
    current = digest()
    previous = None
    if os.path.exists(target):
        previous = open(target, encoding="utf-8").read().strip()
    if previous == current:
        return                      # unchanged: leave mtime alone, nothing rebuilds
    os.makedirs(os.path.dirname(target), exist_ok=True)
    with open(target, "w", encoding="utf-8") as fh:
        fh.write(current + "\n")
    print(f"corpus changed — stamp updated ({target})", file=sys.stderr)


if __name__ == "__main__":
    main()
