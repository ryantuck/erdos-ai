# Fable Review Run

Instructions for running the Fable review pipeline on Erdős problem **NUM** in this repo.
You are a PhD-level mathematician and Lean 4 expert. Do the FULL pipeline — no shortcuts.
Do NOT commit or push; the orchestrator handles git.

## Step 1 — Read the checklist and inputs

Read `FABLE_REVIEW.md` IN FULL and follow it exactly, including its output format. Then read:

- `conjectures/NUM.lean` — **the artifact under review**, always. There is no styled
  variant in this pipeline.
- `ai-review/NUM.md` — prior review, if one exists (audit, don't trust). Legacy: it was
  written against a styled copy, so line numbers will not match.

Read `fable-review/1000.md` and `fable-review/1005.md` as exemplars of expected depth and
format, including the Addendum sections documenting applied fixes. Read them for *depth*,
not for path conventions — both predate this pipeline and review a `deepmind/` file.

`conjectures/NUM.lean` is raw first-pass output: multiple imports, no copyright header, no
`@[category …]` attributes, and bare `:= sorry` are all normal and none of them are
defects. Judge soundness, not style. Direct-assertion form for a *solved* problem is
acceptable if the polarity is the true direction; wrong polarity IS a defect.

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
- **Part D:** actually run the static grep/awk commands and report results.
- **Part E:** audit the prior ai-review claim by claim — re-derive its mathematical
  arguments. Recurring prior-review failure patterns found so far: inventing a
  discrepancy and excusing it asymptotically (1000); unsound `sSup`/boundedness arguments
  (1005); wrong claims about Mathlib semantics, e.g. measures of non-measurable sets
  (1002); endorsing an encoding that contradicts its own reading of the source (1005);
  claiming data is unavailable that is in fact recoverable (1001). Scrutinize these
  classes especially. If no `ai-review/NUM.md` exists, note that and skip Part E.

## Step 4 — Apply fixes

Following the precedent of the 1000/1005 Addenda, write the fixed file to
`conjectures-v2/NUM.lean`. **Leave `conjectures/NUM.lean` untouched** — the before/after
pair is the point, and the input must stay immutable (`GAME_PLAN.md` §3). Start from a
copy of the input and apply:

- **[defect]-class findings (Part A): FIX the statement per your analysis** — correctness
  is highest priority. Flag clearly that the fix is not compile-verified.
- Citation/docstring enrichment recoverable from the archived page: missing reference
  keys as honest stubs, status updates, remarks worth recording, OEIS/cross-references.
- Textual consistency fixes (e.g. redundant namespace qualification under an existing
  `open`).
- Variants CONFIRMED by the recovered page content, using only constructs already present
  in the file, with a docstring and `by sorry`, matching the surrounding file's style. If a
  page-stated bound is literally false at small parameters (cf. 1004's EPS87 bound),
  formalize the corrected version and document the counterexample in the docstring.
- SKIP compiler-dependent changes (e.g. removing `noncomputable`) — note them as
  deferred.
- Do not add copyright headers, `@[category …]`/AMS attributes, or otherwise restyle
  toward the upstream repo. That effort is archived under `deepmind/` and is not part of
  this pipeline.

## Step 5 — Write output

Write `fable-review/NUM.md` in the `FABLE_REVIEW.md` output format, PLUS an
"## Addendum: source recovery and fixes applied" section documenting what was recovered
from which log file (with agreement notes for multiple captures), and each fix
applied/skipped with rationale.

## Final report

Return: verdict + confidence; the problem's one-line statement; every [defect] found
(with whether fixed); notable prior-review audit findings; what was recovered from logs
vs still DEFERRED; list of files you modified. You should have written exactly two:
`fable-review/NUM.md` and `conjectures-v2/NUM.lean`.
