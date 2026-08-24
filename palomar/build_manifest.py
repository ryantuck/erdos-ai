#!/usr/bin/env python3
"""Regenerate palomar/challenges.json from the repository contents.

The manifest is derived data: it maps every Erdős problem to the module holding
its best available formal statement, the theorem names declared there, and the
review provenance. Run this after adding or revising any conjectures-v2/ file.

    python3 palomar/build_manifest.py

Lean comments are stripped before scanning, so prose such as "the theorem below
asserts..." inside a docstring is not mistaken for a declaration.
"""

import json
import os
import re
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "palomar", "challenges.json")
DEFAULT_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(theorem|lemma)\s+([^\s:({\[]+)', re.M)
DEFN = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(def|abbrev|opaque)\s+([^\s:({\[]+)', re.M)
SPLIT = re.compile(r'(?m)^(?=\s*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*'
                   r'(?:theorem|lemma|def|abbrev|opaque|instance|structure|inductive)\b)')


def strip_comments(s):
    """Drop Lean block comments (/- -/, nestable, including /-! and /--) and -- lines."""
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if s.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if s.startswith("-/", i) and depth:
            depth -= 1
            i += 2
            continue
        if depth:
            out.append("\n" if s[i] == "\n" else " ")
            i += 1
            continue
        if s.startswith("--", i):
            j = s.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


def front_matter(path):
    """Read the YAML header of a review note, falling back to a bolded Verdict line."""
    if not os.path.exists(path):
        return None
    txt = open(path, encoding="utf-8").read()
    out = {}
    m = re.search(r'^---\n(.*?)\n---', txt, re.S)
    if m:
        for line in m.group(1).split("\n"):
            if ":" in line:
                k, v = line.split(":", 1)
                out[k.strip()] = v.strip()
    if "verdict" not in out:
        m2 = re.search(r'\*\*Verdict:?\*\*:?\s*([A-Z][A-Z ]+)', txt)
        if m2:
            out["verdict"] = m2.group(1).strip()
    return out or None


CORPUS_DIRS = ["conjectures", "conjectures-v2", "conjectures-v2-haiku", "fable-review", "haiku-review"]


def corpus_revision():
    """Last commit that touched the corpus, not HEAD.

    Pinning HEAD would make this file churn on every unrelated commit: commit,
    re-run, hash differs, working tree dirty again. This changes only when the
    data it describes actually changes.
    """
    out = subprocess.run(["git", "-C", ROOT, "log", "-1", "--format=%h", "--"] + CORPUS_DIRS,
                         capture_output=True, text=True)
    return out.stdout.strip() or "unknown"


def main():
    commit = corpus_revision()
    problems = {}
    for n in range(1, 1180):
        v2 = os.path.join(ROOT, "conjectures-v2", f"{n}.lean")
        v1 = os.path.join(ROOT, "conjectures", f"{n}.lean")
        if os.path.exists(v2):
            path, module, pas = v2, f'ConjecturesV2.«{n}»', "second-pass (reviewed)"
        elif os.path.exists(v1):
            path, module, pas = v1, f'conjectures.«{n}»', "first-pass (unreviewed)"
        else:
            continue

        raw = open(path, encoding="utf-8").read()
        code = strip_comments(raw)
        rec = {
            "problem": n,
            "module": module,
            "file": os.path.relpath(path, ROOT),
            "source_pass": pas,
            "theorems": [m.group(2) for m in DECL.finditer(code)],
            "sorry_placeholders": len(re.findall(r'\bsorry\b', code)),
            "url": f"https://www.erdosproblems.com/{n}",
        }

        holes = []
        for blk in SPLIT.split(code):
            m = DEFN.match(blk)
            if m and re.search(r'\bsorry\b', blk):
                holes.append(m.group(2))
        if holes:
            rec["definition_holes"] = holes
            rec["caveat"] = ("One or more definitions in this module are themselves "
                             "`sorry`; statements quantifying over them are vacuous or "
                             "ill-defined until fixed.")

        for key, d in (("review", "fable-review"), ("benchmark_review", "haiku-review")):
            fm = front_matter(os.path.join(ROOT, d, f"{n}.md"))
            if fm:
                keep = ("verdict", "confidence", "reviewer_model", "source_recovered", "defects")
                rec[key] = {k: fm[k] for k in keep if k in fm and fm[k]}

        problems[str(n)] = rec

    doc = {
        "$comment": ("Machine-readable map of the Erdős problem challenge corpus. Generated "
                     "by palomar/build_manifest.py from the repository contents; do not "
                     "hand-edit. Every theorem listed here is a CHALLENGE statement whose "
                     "proof is `sorry`. See PALOMAR.md."),
        "generated_from_commit": commit,
        "permitted_axioms_default": DEFAULT_AXIOMS,
        "comparator_config_shape": {
            "challenge_module": "<module>",
            "solution_module": "<your solution module>",
            "theorem_names": ["<names>"],
            "permitted_axioms": DEFAULT_AXIOMS,
        },
        "problems": problems,
    }
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(doc, fh, indent=1, ensure_ascii=False)
    print(f"wrote {OUT}: {len(problems)} problems, "
          f"{sum(len(p['theorems']) for p in problems.values())} theorems, "
          f"{sum(1 for p in problems.values() if 'definition_holes' in p)} with definition holes")


if __name__ == "__main__":
    main()
