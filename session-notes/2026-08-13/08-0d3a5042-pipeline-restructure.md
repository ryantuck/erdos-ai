# Session 8 — `0d3a5042-9840-4891-bf65-58632d45ef0d`

*2026-08-13, ~17:56 onward. The session that shipped nine days of uncommitted work and
then rebuilt the project's shape around a single pipeline.*

## One-line story

Started as "what's the git status" and became six merged PRs: the Aug 4 work landed, the
program got a written plan, and the plan was then rewritten twice as the goal clarified —
ending with the DeepMind effort archived and the pipeline reduced to one input directory,
one output directory, one toolchain.

## What shipped

| PR | Commit | What |
|---|---|---|
| #3 | `25712b4e` | The Aug 4 work — `conjectures-v2/` (100 files), `SETUP_LEAN_ENV.md`, the `ErdosV2` lib. Uncommitted for nine days. |
| #4 | `0473c145` | `GAME_PLAN.md` — the program-level plan that didn't exist |
| #5 | `d7ed0d57` | Scoped the concurrency rule to model calls; documented the `deepmind/` import rewrite |
| #6 | `8dcf6691` | Split `conjectures-v2/` into `conjectures-v2/` + `deepmind-v2/` by build environment |
| #7 | `641e961e` | **Redefined the pipeline** as `conjectures/` → review → `conjectures-v2/` |
| #8 | `d7f65430` | Archived the DeepMind effort under `deepmind/` — 2501 renames |

Top level went 46 entries → 33. `master` ended at `3ee652c8`.

## The arc that matters

The plan was written three times, because the goal got sharper each time:

1. **First version (#4)** encoded the batch-1 rule: review `deepmind/N.lean` when it
   exists, else `conjectures/N.lean`. Faithful to what had been done.
2. **#6** noticed that rule forces a mixed output directory — 67 files needing the sibling
   checkout, 33 building locally — and split the output to match.
3. **#7** got the actual goal from the user: the pipeline is
   `erdosproblems.com/N → conjectures/N.lean → Fable review → conjectures-v2/N.lean`,
   uniformly. That deleted the input branch, and with it the 67/33 split, the import
   rewrite, the restyling drift check, and the entire second toolchain.

**#6 was work in the wrong direction.** It carefully engineered a two-directory output for
a distinction that #7 removed a few hours later. It wasn't wasted — `deepmind-v2/` is the
right home for those 67 files now that they're archived, and it surfaced the broken
`lake build ErdosV2` — but the lesson is real: *establish the intended pipeline before
optimizing the current one.* Three of the six PRs exist only because the plan was written
from the code rather than from the goal.

## Findings

**Verified against disk and git, correcting the record:**

- `fable-review/` covers **1000–1100 (101 problems)**, not 1001–1100. Problem 1000 was the
  pilot.
- **No coverage gap near 1080.** 1037 and 1048 lack their own `Fable review <N>` commit
  subject but landed together in `0c24b220`.
- **Opus 5 produced none of the review corpus.** All 102 review commits are
  `Co-Authored-By: Claude Fable 5`. Batch 1 is a clean single-model baseline.
- `conjectures/` is exactly 1–1179, no gaps, nothing extra.

**Found by building, not reading:**

- All 808 files in `deepmind/deepmind/` carry the pre-rename import
  `FormalConjectures.Util.ProblemImports`. Building one against a current upstream
  checkout fails at import resolution before any mathematics is checked. Found when 1103
  failed; it built clean in 362s once rewritten.
- `lake build ErdosV2` had never worked — the Lake glob needs a stub root module
  (`ConjecturesV2.lean`, mirroring `conjectures.lean`) and there wasn't one. Only
  per-module targets were ever used, so nobody hit it.
- The Makefile's styling rule invoked `ADHERE_TO_DEEPMIND_STYLE_GUIDE.md`, a filename that
  has never existed in this repo. That rule could not have run as written.

**Compile baseline (no review work was run):**

| Set | Where | Result |
|---|---|---|
| 1101–1105 inputs | local + sibling | all 5 pass |
| `conjectures-v2/` 33 | `lake build ErdosV2` | 2733 jobs, 113 `sorry`, 0 non-sorry |
| `deepmind-v2/` 67 | sibling, one target list | 8110 jobs, 0 errors, 0 warnings |

## Two numbers I got wrong

- Told the user **437** problems take the `deepmind/` input path. The real figure is
  **741**. Recomputed and corrected in-session; it made the pipeline change more
  consequential than I'd represented.
- Counted the 67 styled second-pass files as *done*. They were reviewed against
  `deepmind/N.lean`, so under the new pipeline they aren't outputs of it. Corrected
  accounting: **33 done, 1146 remaining**, of which 68 have legacy review notes.

## Process notes

- **The memory directory worked.** Session 7 wrote three `project` memories; this session
  opened with the state already in context and went straight to committing — no transcript
  archaeology, which is what sessions 3–5 spent most of their budget on.
- **`/tmp` still isn't storage.** Session 7's seven notes were written to its scratchpad
  and reaped within the hour; this session reconstructed all seven from `Write`/`Edit`
  tool inputs in session 7's `.jsonl`. That is exactly the archaeology `00-SYNTHESIS.md`
  criticizes. Hence this directory, in the repo.
- **The `-P2` rule got scoped correctly only after being applied wrongly.** The 33 local
  builds were throttled to two at a time for no reason — `lake` costs CPU, not tokens. The
  concurrency limit governs model calls and nothing else (#5).

## State at close

- `master` = `3ee652c8`, clean. Top level 33 entries.
- `conjectures-v2/` = 33 files. **1146 remaining.** First batch is 1101–1179.
- **No review work has been run.** Everything so far is plan, restructure, and baseline.
- `review-one.sh` exists only as a sketch inside `GAME_PLAN.md` §5 — never written to
  disk, never run, `--output-format json` field names unverified.
- Seven merged branches still exist locally and on the remote, never pruned.
