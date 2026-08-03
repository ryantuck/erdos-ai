# Fable Review Run

Instructions for running the Fable review pipeline on Erdős problem **NUM** in this repo.
You are a PhD-level mathematician and Lean 4 expert. Do the FULL pipeline — no shortcuts.
Do NOT commit or push; the orchestrator handles git.

## Step 1 — Read the checklist and inputs

Read `FABLE_REVIEW.md` IN FULL and follow it exactly, including its output format. Then read:

- `deepmind/NUM.lean` — the artifact under review
- `conjectures/NUM.lean` — raw first-pass; diff against styled to check nothing drifted
- `ai-review/NUM.md` and `reviews/NUM.md` — prior reviews (audit, don't trust)

Read `fable-review/1000.md` and `fable-review/1005.md` as exemplars of expected depth and
format, including the Addendum sections documenting applied fixes.

**If `deepmind/NUM.lean` does not exist** (problem was formalized upstream before this
project; no prior reviews exist either): the artifact under review is
`conjectures/NUM.lean`. Skip the raw-vs-styled diff; adapt Part E to audit the file's
docstring claims against the recovered source; note in the review header that the
authoritative upstream artifact lives in google-deepmind/formal-conjectures and is not
present in this repo. Raw files may legitimately have multiple imports and bare
`:= sorry` — judge soundness, not style. Direct-assertion form for a *solved* problem is
acceptable raw style if the polarity is the true direction; wrong polarity IS a defect.

## Step 2 — Source recovery (do NOT attempt network)

erdosproblems.com is blocked by this container's network gateway (CONNECT 403 for every
tool) — do not waste time on curl/WebFetch. Recover the archived website content from the
session logs instead; the original pipeline sessions fetched the live pages and their
JSONL transcripts contain the HTML:

```bash
grep -l "erdosproblems.com/NUM" claude-session-logs/*.jsonl claude-session-logs-formal-conjectures/*.jsonl
```

Parse candidates with python3, looking for large user/tool_result messages containing
`problem-box` / `problem-text` HTML divs. Extract: the verbatim problem statement, the
status banner (OPEN / SOLVED / PROVED (LEAN) with tooltip text), the remarks section
(partial results, related work), all citation keys (`[XxNN]` links), tags, OEIS
references, cross-referenced problem numbers, and the page-edition/accessed date. Prefer
the log with the fullest page; when multiple captures exist, note whether they agree.

Bibliographic data (journal/volume/pages) is often recoverable too — check, in order:
1. `/latex/NUM` or `/bibs/` fetch results in the logs (search for `latex/NUM`, `bibitem`);
2. upstream formal-conjectures file contents captured in
   `claude-session-logs-formal-conjectures/` (full reference blocks for shared keys like
   `[Er85e]` often appear in neighboring problems' files);
3. sibling files in this repo already carrying the same key (`grep -rn 'KEY' deepmind/
   conjectures/`).

Record provenance for everything recovered. If the page can be recovered, upgrade the
relevant checklist items from DEFERRED to source-verified; otherwise mark DEFERRED
honestly. NEVER fabricate bibliographic data — stubs only, with provenance noted.

## Step 3 — Full review

Work through Parts A–E of `FABLE_REVIEW.md` rigorously:

- **Part A:** back-translate the Lean independently; check every listed semantics trap
  explicitly (ℕ subtraction/division, division-by-zero, `range` off-by-ones, vacuous
  quantifiers, filter encodings, `StrictMono` vs `Monotone`); verify `answer()` shape and
  polarity by hand against the question form and solution status; check the statement is
  not vacuous/trivial.
- **Restyling drift check:** diff the raw and styled docstrings as well as the code. The
  1005 defect (open question silently converted to a bare assertion, question sentence
  dropped from the docstring) entered during restyling — look for meaning changes, not
  just code changes.
- **Part D:** actually run the static grep/awk commands and report results.
- **Part E:** audit the prior ai-review claim by claim — re-derive its mathematical
  arguments. Recurring prior-review failure patterns found so far: inventing a
  discrepancy and excusing it asymptotically (1000); unsound `sSup`/boundedness arguments
  (1005); wrong claims about Mathlib semantics, e.g. measures of non-measurable sets
  (1002); endorsing an encoding that contradicts its own reading of the source (1005);
  claiming data is unavailable that is in fact recoverable (1001). Scrutinize these
  classes especially.

## Step 4 — Apply fixes

Following the precedent of the 1000/1005 Addenda, apply fixes to the Lean file under
review:

- **[defect]-class findings (Part A): FIX the statement per your analysis** — correctness
  is highest priority. Flag clearly that the fix is not compile-verified.
- Citation/docstring enrichment recoverable from the archived page: missing reference
  keys as honest stubs, status updates, remarks worth recording, OEIS/cross-references.
- Textual consistency fixes (e.g. redundant namespace qualification under an existing
  `open`).
- Variants CONFIRMED by the recovered page content, using only constructs already present
  in the file, named `erdos_NUM.variants.<descriptor>` (styled files) with docstring,
  `@[category ..., AMS ...]`, and `by sorry`; raw-file style for raw files. If a
  page-stated bound is literally false at small parameters (cf. 1004's EPS87 bound),
  formalize the corrected version and document the counterexample in the docstring.
- SKIP compiler-dependent changes (e.g. removing `noncomputable`) — note them as
  deferred.
- Do not touch copyright/imports/namespace/AMS styling.

## Step 5 — Write output

Write `fable-review/NUM.md` in the `FABLE_REVIEW.md` output format, PLUS an
"## Addendum: source recovery and fixes applied" section documenting what was recovered
from which log file (with agreement notes for multiple captures), and each fix
applied/skipped with rationale.

## Final report

Return: verdict + confidence; the problem's one-line statement; every [defect] found
(with whether fixed); notable prior-review audit findings; what was recovered from logs
vs still DEFERRED; list of files you modified.
