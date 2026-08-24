#!/usr/bin/env python3
"""Build site/data.json — the dataset the interactive explorer reads.

Source of truth is palomar/challenges.json (module, theorem names, review
provenance). This adds what a human browsing needs and the manifest omits: a
readable statement summary, the problem's solution status, and its subject tags,
all pulled out of the Lean module docstrings.

    python3 site/build_data.py

Docstring shape varies across the corpus — the first pass and the reviewed
second pass write headers differently, and neither is machine-generated — so
extraction is best-effort with layered fallbacks. Coverage is reported on stderr
and recorded in the output under `extraction`, so the explorer can be honest
about which fields were recovered rather than silently showing blanks.
"""

import json
import os
import re
import subprocess
import sys

try:
    import yaml
except ImportError:
    sys.exit("needs PyYAML: pip install pyyaml")

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(ROOT, "palomar", "challenges.json")
SITE_META = os.path.join(ROOT, "source-erdos-problems.yaml")
CLASSES = os.path.join(ROOT, "erdos_problem_classifications.yml")
OUT = os.path.join(ROOT, "site", "data.json")


def load_site_metadata():
    """Problem status, prize, tags and OEIS refs from the collection's own metadata.

    This is a snapshot of the upstream metadata mirror, so its `last_update`
    stamps are older than the reviewed corpus's status cross-checks. Where the
    reviewed pass recorded a status in its docstring, that wins.
    """
    meta = {}
    if os.path.exists(SITE_META):
        for entry in yaml.safe_load(open(SITE_META, encoding="utf-8")) or []:
            try:
                n = int(str(entry.get("number", "")).strip())
            except ValueError:
                continue
            if n in meta:          # duplicate numbers exist; first wins
                continue
            st = entry.get("status") or {}
            meta[n] = {
                "site_status": (st.get("state") or "").strip(),
                "status_updated": str(st.get("last_update") or ""),
                "prize": (entry.get("prize") or "").strip(),
                "tags": [t for t in (entry.get("tags") or []) if t],
                "oeis": [o for o in (entry.get("oeis") or []) if o],
                "upstream_formalized": ((entry.get("formalized") or {}).get("state") or "").strip(),
            }
    classes = {}
    if os.path.exists(CLASSES):
        doc = yaml.safe_load(open(CLASSES, encoding="utf-8")) or {}
        for n, dom in (doc.get("problems") or {}).items():
            try:
                classes[int(n)] = str(dom)
            except (TypeError, ValueError):
                continue
    return meta, classes

# Module docstring /-! ... -/ or a doc comment /-- ... -/
MOD_DOC = re.compile(r'/-!(.*?)-/', re.S)
DOC = re.compile(r'/--(.*?)-/', re.S)

STATUS_PATTERNS = [
    (re.compile(r'\*\*Status:\s*([A-Za-z ]+?)\*\*'), 1),
    (re.compile(r'Status:\s*\*\*([A-Za-z ]+?)\*\*'), 1),
    (re.compile(r'Status\s*\([^)]*\):\s*([A-Z][A-Z ]+)'), 1),
    (re.compile(r'\bThe problem is (OPEN|SOLVED|PROVED|DISPROVED)\b'), 1),
    (re.compile(r'\b(DISPROVED|PROVED|SOLVED|OPEN)\b(?=[\s.,—-])'), 1),
]

TAGS = re.compile(r'^\s*Tags?:\s*(.+)$', re.M)
# Reviewed-pass docstrings quote the source page, but the lead-in wording varies
# ("Statement (verbatim from the site):", "**Problem (verbatim from the source
# page):**", "Verbatim statement (recovered from ...):"). Match any of them and
# take the quoted text that follows.
VERBATIM = re.compile(r'[*_ ]*(?:Statement|Problem|Verbatim statement)[^\n:]{0,80}'
                      r'verbatim[^\n:]{0,80}:[*_ ]*\s*[""]?"?(.*?)"', re.S | re.I)
# The header may carry a bracketed citation list that wraps across lines;
# swallow it so the statement is captured rather than the reference keys.
PROBLEM_HDR = re.compile(r'Erd(?:ő|o)s Problem #?\d+\s*(?:\([^)]*\))?\s*(?:\[[^\]]*\])?\s*:?\s*(.*)', re.S)
HEADING = re.compile(r'^#\s*(Erd(?:ő|o)s Problem.*)$', re.M)


def clean(text, limit=460):
    """Collapse a chunk of Lean docstring prose into one readable paragraph."""
    if not text:
        return ""
    t = re.sub(r'\\\[|\\\]|\\\(|\\\)', " ", text)      # LaTeX display/inline delimiters
    t = re.sub(r'\$+', "", t)                            # $ math delimiters
    t = re.sub(r'\\(?:lvert|rvert|vert)', "|", t)
    t = re.sub(r'\\(?:leq|le)\b', "≤", t)
    t = re.sub(r'\\(?:geq|ge)\b', "≥", t)
    t = re.sub(r'\\(?:cdots|ldots|dots)\b', "…", t)
    t = re.sub(r'\\(?:subset|subseteq)\b', "⊂", t)
    t = re.sub(r'\\in\b', "∈", t)
    t = re.sub(r'\\mathbb\{([A-Z])\}', r'\1', t)
    t = re.sub(r'\\(?:frac|tfrac)\{([^{}]*)\}\{([^{}]*)\}', r'(\1)/(\2)', t)
    t = re.sub(r'\\[a-zA-Z]+', " ", t)                   # any remaining macro
    t = re.sub(r'[{}]', "", t)
    t = re.sub(r'\s+', " ", t).strip()
    if len(t) > limit:
        cut = t[:limit]
        sp = cut.rfind(" ")
        t = (cut[:sp] if sp > limit * 0.6 else cut).rstrip(" ,;:") + "…"
    return t


def summarize(src, n=None):
    """Return (summary, status, tags, heading) extracted from a Lean file."""
    blocks = MOD_DOC.findall(src) or []
    doc_blocks = DOC.findall(src) or []
    # Prefer the docstring headed by THIS problem's number. Files cross-reference
    # sibling problems ("the same encoding appears in Erdős Problem #7"), so
    # matching the first block mentioning any problem picks up the neighbour's
    # header and yields a summary of nothing.
    own = []
    if n is not None:
        # Headers are not uniform: "Erdős Problem #110", "Problem #110",
        # "Erdős-Hajnal-Szemerédi Conjecture (Problem #110)".
        own_re = re.compile(r'(?:Erd(?:ő|o)s[- ])?Problem #?%d\b' % n)
        own = [b for b in blocks + doc_blocks if own_re.search(b)]
    candidates = own or [b for b in blocks + doc_blocks
                         if re.search(r'(?:Erd(?:ő|o)s )?Problem #?\d', b)]
    body = candidates[0] if candidates else (blocks[0] if blocks else
                                            (doc_blocks[-1] if doc_blocks else ""))
    whole = "\n".join(blocks + doc_blocks)

    heading = ""
    m = HEADING.search(body)
    if m:
        heading = clean(m.group(1), 90)

    summary = ""
    m = VERBATIM.search(whole)                     # reviewed pass quotes the site verbatim
    if m:
        summary = clean(m.group(1))
    if not summary and body:
        after = body
        m = (re.search(r'(?:Erd(?:ő|o)s[- ])?Problem #?%d\b\s*\)?\s*(?:\([^)]*\))?'
                       r'\s*(?:\[[^\]]*\])?\s*:?\s*(.*)' % n, body, re.S)
             if n is not None else None) or PROBLEM_HDR.search(body)
        if m:
            after = m.group(1)
        else:
            after = HEADING.sub("", body)
        # First substantive paragraph. Reviewed-pass docstrings open with
        # boilerplate (a *Reference:* line, a Status banner, a bare heading)
        # before reaching the statement, so skip those rather than showing them.
        skip = re.compile(r'^(reference|tags?|status|source|see also|https?:|'
                          r'erd(?:ő|o)s problem\b|accessed\b|page edition\b)', re.I)
        for para in re.split(r'\n\s*\n', after.strip()):
            c = clean(para)
            probe = c.lstrip("*_# ").strip()
            if len(c) > 40 and not skip.match(probe):
                summary = c
                break
        if not summary:
            summary = clean(after)

    status = ""
    for pat, grp in STATUS_PATTERNS:
        m = pat.search(whole)
        if m:
            status = m.group(grp).strip().upper()
            break
    if status:
        status = re.sub(r'\s+', " ", status)
        for canon in ("DISPROVED", "PROVED", "SOLVED", "OPEN"):
            if canon in status:
                status = canon
                break
        else:
            status = ""

    tags = []
    m = TAGS.search(whole)
    if m:
        tags = [t.strip().rstrip(".") for t in re.split(r'[,|]', m.group(1)) if t.strip()]
        tags = [t for t in tags if 2 < len(t) < 40][:6]

    return summary, status, tags, heading


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
    if not os.path.exists(MANIFEST):
        sys.exit("missing palomar/challenges.json — run palomar/build_manifest.py first")
    manifest = json.load(open(MANIFEST, encoding="utf-8"))

    commit = corpus_revision()

    site_meta, classes = load_site_metadata()

    problems, got_summary, got_status, got_tags = [], 0, 0, 0
    for key in sorted(manifest["problems"], key=int):
        rec = manifest["problems"][key]
        n = rec["problem"]
        path = os.path.join(ROOT, rec["file"])
        src = open(path, encoding="utf-8").read() if os.path.exists(path) else ""
        doc_summary, doc_status, doc_tags, heading = summarize(src, n)
        meta = site_meta.get(n, {})

        summary = doc_summary
        # Reviewed-pass docstrings cross-check status against the mirror at a later
        # date than this snapshot, so they take precedence when they recorded one.
        status = doc_status or (meta.get("site_status", "") or "").upper()
        status_source = "review docstring" if doc_status else ("collection metadata" if status else "")
        tags = meta.get("tags") or doc_tags

        got_summary += bool(summary)
        got_status += bool(status)
        got_tags += bool(tags)

        review = rec.get("review", {})
        bench = rec.get("benchmark_review", {})
        defects = review.get("defects", "")
        if isinstance(defects, str):
            defects = [d.strip() for d in defects.strip("[]").split(",") if d.strip()]

        problems.append({
            "n": rec["problem"],
            "module": rec["module"],
            "file": rec["file"],
            "pass": "v2" if rec["source_pass"].startswith("second") else "v1",
            "summary": summary,
            "heading": heading,
            "status": status,
            "status_source": status_source,
            "status_updated": meta.get("status_updated", ""),
            "prize": meta.get("prize", ""),
            "oeis": meta.get("oeis", []),
            "upstream_formalized": meta.get("upstream_formalized", ""),
            "domain": classes.get(n, ""),
            "tags": tags,
            "theorems": rec["theorems"],
            "sorries": rec["sorry_placeholders"],
            "holes": rec.get("definition_holes", []),
            "verdict": review.get("verdict", ""),
            "confidence": review.get("confidence", ""),
            "reviewer": review.get("reviewer_model", ""),
            "sourced": review.get("source_recovered", ""),
            "defects": defects,
            "bench_verdict": bench.get("verdict", ""),
            "review_file": f"fable-review/{rec['problem']}.md" if review else "",
            "bench_file": f"haiku-review/{rec['problem']}.md" if bench else "",
            "url": rec["url"],
        })

    total = len(problems)
    doc = {
        "generated_from_commit": commit,
        "repo": "https://github.com/ryantuck/erdos-ai",
        "counts": {
            "problems": total,
            "reviewed": sum(1 for p in problems if p["verdict"]),
            "needs_revision": sum(1 for p in problems if p["verdict"] == "NEEDS REVISION"),
            "accept_nits": sum(1 for p in problems if p["verdict"] == "ACCEPT WITH NITS"),
            "v2": sum(1 for p in problems if p["pass"] == "v2"),
            "theorems": sum(len(p["theorems"]) for p in problems),
            "sorries": sum(p["sorries"] for p in problems),
            "with_holes": sum(1 for p in problems if p["holes"]),
            "with_prize": sum(1 for p in problems if p["prize"]),
        },
        "extraction": {
            "note": ("Statement summaries are best-effort extractions from heterogeneous "
                     "Lean docstrings; a blank means the extractor could not find one, not "
                     "that the problem lacks one. Status, prize, tags and OEIS refs come "
                     "from source-erdos-problems.yaml, a snapshot of the collection's own "
                     "metadata, except where a reviewed-pass docstring recorded a fresher "
                     "status \u2014 see each problem's status_source."),
            "summary_coverage": round(got_summary / total, 3),
            "status_coverage": round(got_status / total, 3),
            "tags_coverage": round(got_tags / total, 3),
        },
        "problems": problems,
    }
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(doc, fh, ensure_ascii=False, separators=(",", ":"))

    print(f"wrote {OUT}: {total} problems, {os.path.getsize(OUT)//1024} KB", file=sys.stderr)
    print(f"  summary extracted for {got_summary}/{total} ({got_summary/total:.1%})", file=sys.stderr)
    print(f"  status  extracted for {got_status}/{total} ({got_status/total:.1%})", file=sys.stderr)
    print(f"  tags    extracted for {got_tags}/{total} ({got_tags/total:.1%})", file=sys.stderr)


if __name__ == "__main__":
    main()
