#!/usr/bin/env python3
"""Smoke-test the generated site data. Run via `make site-check`.

Catches the failure modes that matter for a static site whose data is derived:
data that drifted from the corpus, rows pointing at files that no longer exist,
verdict values the explorer's stylesheet has no colour for, and hardcoded
figures in the narrative page that the corpus has since outgrown.

Exits non-zero on failure so it can gate a deploy.
"""

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "site", "data.json")
MANIFEST = os.path.join(ROOT, "palomar", "challenges.json")

KNOWN_VERDICTS = {"", "ACCEPT", "ACCEPT WITH NITS", "NEEDS REVISION"}
failures, warnings = [], []


def check(cond, msg):
    if not cond:
        failures.append(msg)


def warn(cond, msg):
    if not cond:
        warnings.append(msg)


def main():
    if not os.path.exists(DATA):
        sys.exit("site/data.json missing — run `make site`")
    data = json.load(open(DATA, encoding="utf-8"))
    manifest = json.load(open(MANIFEST, encoding="utf-8"))
    problems = data["problems"]
    counts = data["counts"]

    # 1. shape
    check(len(problems) == 1179, f"expected 1179 problems, got {len(problems)}")
    check(len({p["n"] for p in problems}) == len(problems), "duplicate problem numbers in data.json")
    check(sorted(p["n"] for p in problems) == list(range(1, 1180)), "problem numbers are not exactly 1..1179")

    # 2. data.json agrees with the manifest it was derived from
    check(len(problems) == len(manifest["problems"]),
          "data.json and palomar/challenges.json disagree on problem count — rerun `make site`")
    for p in problems[:]:
        m = manifest["problems"].get(str(p["n"]))
        if m and m["theorems"] != p["theorems"]:
            failures.append(f"problem {p['n']}: theorem list differs from the manifest")
            break

    # 3. every referenced file is really on disk
    missing = [p["n"] for p in problems if not os.path.exists(os.path.join(ROOT, p["file"]))][:5]
    check(not missing, f"data.json points at missing Lean files: {missing}")
    bad_review = [p["n"] for p in problems
                  if p["review_file"] and not os.path.exists(os.path.join(ROOT, p["review_file"]))][:5]
    check(not bad_review, f"data.json points at missing review notes: {bad_review}")

    # 4. values the explorer's CSS and filters know how to render
    unknown = {p["verdict"] for p in problems} - KNOWN_VERDICTS
    check(not unknown, f"unknown verdict values (explorer has no styling for these): {sorted(unknown)}")
    check(all(isinstance(p["defects"], list) for p in problems), "defects must be a list on every problem")
    check(all(isinstance(p["theorems"], list) and p["theorems"] for p in problems),
          "every problem must declare at least one theorem")

    # 5. internal consistency of the summary counts the masthead shows
    check(counts["reviewed"] == sum(1 for p in problems if p["verdict"]), "counts.reviewed is stale")
    check(counts["needs_revision"] == sum(1 for p in problems if p["verdict"] == "NEEDS REVISION"),
          "counts.needs_revision is stale")
    check(counts["v2"] == sum(1 for p in problems if p["pass"] == "v2"), "counts.v2 is stale")
    check(counts["with_holes"] == sum(1 for p in problems if p["holes"]), "counts.with_holes is stale")

    # 6. the pages themselves
    exp = os.path.join(ROOT, "explorer.html")
    check(os.path.exists(exp), "explorer.html is missing")
    if os.path.exists(exp):
        src = open(exp, encoding="utf-8").read()
        check('fetch("site/data.json")' in src, "explorer.html no longer fetches site/data.json")
        check("<title>" in src, "explorer.html has no <title>")

    # 7. the narrative page hardcodes figures; flag any that the corpus outgrew
    idx = os.path.join(ROOT, "index.html")
    if os.path.exists(idx):
        text = open(idx, encoding="utf-8").read()
        for label, value in (("problems reviewed", counts["reviewed"]),
                             ("needs-revision count", counts["needs_revision"]),
                             ("corrected files", counts["v2"])):
            warn(str(value) in text,
                 f"index.html does not mention the current {label} ({value}) — narrative may be stale")

    # 8. extraction quality did not collapse
    warn(data["extraction"]["summary_coverage"] >= 0.90,
         f"statement summaries recovered for only "
         f"{data['extraction']['summary_coverage']:.0%} of problems")

    for w in warnings:
        print(f"warning: {w}", file=sys.stderr)
    for f in failures:
        print(f"FAIL: {f}", file=sys.stderr)

    if failures:
        sys.exit(f"\n{len(failures)} check(s) failed")
    print(f"site-check passed: {len(problems)} problems, {counts['reviewed']} reviewed, "
          f"{counts['with_holes']} with definition holes"
          + (f", {len(warnings)} warning(s)" if warnings else ""))


if __name__ == "__main__":
    main()
