#!/usr/bin/env python3
"""Emit a leanprover/comparator config for one Erdős problem.

The corpus in this repository is the *challenge* half of the Comparator
contract: every theorem is a statement whose proof is `sorry`. This script
writes the JSON config that pairs one of those challenge modules with a
solution module you supply, so Comparator can check that your proof proves
exactly the claimed statement and uses only permitted axioms.

    python3 palomar/make_config.py 90 --solution MySolution
    python3 palomar/make_config.py 90 --solution MySolution -o /tmp/90.json

Nothing here has been executed against Comparator — this repository has no Lean
toolchain installed, and the project defers all compile verification to a
machine that does. Treat the emitted config as unverified until you run it.
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MANIFEST = os.path.join(HERE, "challenges.json")

# The standard classical Lean axiom set, as documented by leanprover/comparator.
DEFAULT_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


def load_manifest():
    if not os.path.exists(MANIFEST):
        sys.exit(f"missing {MANIFEST} — run palomar/build_manifest.py first")
    with open(MANIFEST, encoding="utf-8") as fh:
        return json.load(fh)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("problem", type=int, help="Erdős problem number, 1–1179")
    ap.add_argument("--solution", required=True,
                    help="Lean module name of your solution, e.g. MySolution")
    ap.add_argument("--theorems", nargs="*", default=None,
                    help="subset of theorem names to require (default: all in the module)")
    ap.add_argument("--axioms", nargs="*", default=DEFAULT_AXIOMS,
                    help=f"permitted axioms (default: {' '.join(DEFAULT_AXIOMS)})")
    ap.add_argument("-o", "--out", default=None, help="write here instead of stdout")
    args = ap.parse_args()

    problems = load_manifest()["problems"]
    key = str(args.problem)
    if key not in problems:
        sys.exit(f"no such problem: {args.problem} (valid range 1–1179)")
    rec = problems[key]

    names = args.theorems if args.theorems else rec["theorems"]
    unknown = [n for n in names if n not in rec["theorems"]]
    if unknown:
        sys.exit(f"not declared in {rec['file']}: {', '.join(unknown)}\n"
                 f"available: {', '.join(rec['theorems'])}")

    config = {
        "challenge_module": rec["module"],
        "solution_module": args.solution,
        "theorem_names": names,
        "permitted_axioms": args.axioms,
    }

    text = json.dumps(config, indent=2, ensure_ascii=False) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(text)
        print(f"wrote {args.out}", file=sys.stderr)
    else:
        sys.stdout.write(text)

    if "definition_holes" in rec:
        print(f"\nwarning: problem {args.problem} has definition(s) that are themselves "
              f"`sorry` ({', '.join(rec['definition_holes'])}). Statements quantifying "
              f"over them are vacuous or ill-defined; fix the definition before "
              f"treating a proof of this challenge as meaningful.", file=sys.stderr)
    if rec["source_pass"].startswith("first"):
        print(f"\nnote: problem {args.problem} comes from the unreviewed first pass. "
              f"Roughly a third of reviewed problems needed semantic corrections; "
              f"assume this statement carries the same risk.", file=sys.stderr)


if __name__ == "__main__":
    main()
