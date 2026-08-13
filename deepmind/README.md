# The DeepMind effort (archived)

Everything here belongs to the first route this project took: formalize all 1179 Erdős
problems, restyle them to match [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
and contribute them upstream. That worked — it completed
[Milestone 1](https://github.com/google-deepmind/formal-conjectures/milestone/1) — but
upstream gates every contribution on human review, and the project has since taken an
AI-first route instead.

**Nothing in the live pipeline reads from this directory.** See `../GAME_PLAN.md`; the
pipeline is now `erdosproblems.com/N` → `../conjectures/N.lean` → Fable review →
`../conjectures-v2/N.lean`, with no styled intermediate.

This is kept for provenance, not because it is finished or unfinished. Treat it as frozen.

## Contents

| Path | Count | What it is |
|---|---|---|
| `deepmind/` | 808 | Restyled formalizations. Apache header, `@[category …]`/AMS attributes, `import FormalConjecturesUtil`. Covers 808 of 1179 — the 371 gaps are problems already formalized upstream, which the styling pass skipped. |
| `deepmind-v2/` | 67 | Second-pass Fable-reviewed versions of the styled files, problems 1001–1100. Superseded: the current pipeline re-reviews these from `../conjectures/`. |
| `ai-review/` | 807 | First-pass mathematical reviews, produced by `REVIEW_MATH.md`. Still read as Part E audit material by the live review — see `../FABLE_REVIEW.md`. |
| `reviews/` | 808 | First-pass style/checklist reviews against `CHECKLIST.md`. |
| `ramsey-pr-edits/` | 2 | Session notes from the upstream Ramsey PR. |

## Instructions

- `ADHERE_TO_DEEPMIND_STYLE.md` — the restyling prompt (`conjectures/N.lean` → `deepmind/N.lean`).
- `CHECKLIST.md` — the 60-point PR checklist derived from upstream `AGENTS.md` and `README.md`.
- `REVIEW_MATH.md` — the prompt that produced `ai-review/`.
- `FIX_REVIEW_ISSUES.md` — the fix-application prompt. Written against upstream paths
  (`FormalConjectures/ErdosProblems/N.lean`, `FormalConjecturesForMathlib/`) that do not
  exist in this repo.
- `Makefile` — the styling and stylize-tracking rules, split out of the top-level one.

## Building anything in here

These files import `FormalConjecturesUtil` and only build in a sibling
`../../formal-conjectures` checkout on Lean 4.27.0 — not in this repo, which is on 4.28.0.
`../SETUP_LEAN_ENV.md` has the setup.

One gotcha worth recording: all 808 files in `deepmind/` still carry the pre-rename import
`FormalConjectures.Util.ProblemImports`. Upstream renamed it to `FormalConjecturesUtil`,
so building one against a current checkout fails at import resolution before any
mathematics is checked. Rewrite first:

```bash
sed 's#^import FormalConjectures\.Util\.ProblemImports$#import FormalConjecturesUtil#' \
    deepmind/N.lean > /tmp/N.lean
```

`deepmind-v2/` already has this applied.
