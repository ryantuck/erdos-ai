# Game Plan — Fable Review of All 1179 Erdős Problems

*Written 2026-08-13. Program-level plan. The per-problem procedure lives in
`FABLE_REVIEW.md` (what to check) and `FABLE_REVIEW_RUN.md` (how to run one); this
document is the layer above them: what the whole run is for, what order it goes in, and
how to pay for it without tripping rate limits.*

## 1. Goal

Pass all 1179 problems in `conjectures/` through a two-stroke review, producing a
second-generation dataset in `conjectures-v2/` (plain Mathlib) and `deepmind-v2/`
(styled, upstream-flavored) — mirroring the first pass's `conjectures/` + `deepmind/`
split, so each directory is standalone and builds in exactly one environment.

This is deliberately an **AI-first** route. The DeepMind `formal-conjectures` project
gates every contribution on human review; this project does not, and the output is not
destined for that repo (`FABLE_REVIEW.md:31`). The quality bar is enforced instead by an
adversarial second pass — a different, stronger model re-deriving the mathematics from
the recovered source page and auditing the prior review claim by claim.

Two consequences shape everything below:

- **The dataset is versioned by model generation.** When a new frontier model ships, the
  run is repeated and a v3 produced. So the pipeline must be cheap to re-run end to end,
  and every artifact must record which model produced it.
- **The by-product is a benchmark.** A corpus of 1179 formalizations, each with a
  known-defect record from a stronger reviewer, is a natural benchmark for
  *formalization fidelity* — can a model state a known mathematical claim in Lean without
  changing its meaning? That framing is only worth anything if the defect records are
  consistent and attributable, which is a constraint on the run, not an afterthought.

## 2. Verified state (checked against disk and git, 2026-08-13)

| Directory | Count | Range | Notes |
|---|---|---|---|
| `conjectures/` | **1179** | 1–1179, **no gaps, nothing extra** | first-pass formalizations; the universe |
| `deepmind/` | **808** | 2–1179, sparse | restyled subset; **371 problems have no file here** |
| `ai-review/` | 807 | sparse | first-pass reviews |
| `reviews/` | 808 | sparse | first-pass reviews |
| `fable-review/` | **101** | **1000–1100** | second-pass review notes |
| `conjectures-v2/` | **33** | 1001–1100, sparse | second pass, plain Mathlib — builds here |
| `deepmind-v2/` | **67** | 1001–1100, sparse | second pass, `FormalConjecturesUtil` — builds in sibling |

Three corrections to the working recollection:

1. **The Fable run covered 1000–1100 (101 problems), not 1001–1100.** Problem 1000 was
   the pilot — reviewed and fixed in its own commits (`f879936d`, `ee428d72`) before the
   batch proper began.
2. **There is no gap at ~1080.** All 101 reviewed problems had fixes applied and
   committed. 1037 and 1048 look missing if you grep commit subjects for `Fable review
   <N>`, but they landed together in `0c24b220` ("Fable reviews 1037, 1048; propagate
   Er93 fix to 1029"), and their fixes are present in the files.
3. **No part of the review corpus was done by Opus 5.** Every one of the 102 review
   commits carries `Co-Authored-By: Claude Fable 5`. Opus 5 appears exactly once in this
   repo's history — commit `25712b4e` yesterday, which packaged `conjectures-v2/` and
   wrote no mathematics. Sonnet 4.6 appears once. The reviewer population is homogeneous,
   which is good news for the benchmark framing: batch 1 is a clean single-model baseline.

One real gap: **problem 1000 was reviewed and fixed but never promoted to either v2
directory.** It is picked up by the 901–1000 batch below as promote-only work.

**Net remaining: 1078 to review, 1079 to promote into v2.**

## 3. The unit of work

One problem, one fresh agent session, two strokes:

**Stroke 1 — analyze.** Recover the source page, back-translate the Lean independently,
work Parts A–E of `FABLE_REVIEW.md`, audit the prior `ai-review/` claim by claim. Output
is the verdict and the defect list.

**Stroke 2 — fix and promote.** Apply the fixes, add page-confirmed variants, write
`fable-review/<N>.md` including the Addendum, and write the result to the v2 directory
matching the input: `deepmind/<N>.lean` → `deepmind-v2/<N>.lean`, `conjectures/<N>.lean`
→ `conjectures-v2/<N>.lean`. The destination is determined by the input, never chosen.

**Required when promoting from `deepmind/`: rewrite the import.** All **808** files in
`deepmind/` carry `import FormalConjectures.Util.ProblemImports`, a module that no longer
exists upstream — it was renamed to `FormalConjecturesUtil`. Without the rewrite the
build dies at import resolution before any mathematics is checked (verified 2026-08-13 on
1103). Batch 1 did this during assembly; under the write-to-v2-directly rule it becomes
part of stroke 2:

```bash
sed 's#^import FormalConjectures\.Util\.ProblemImports$#import FormalConjecturesUtil#' \
    deepmind/<N>.lean > deepmind-v2/<N>.lean
```

Files taking the `conjectures/` path import plain `Mathlib.*`, need no rewrite, and are a
straight `cp` into `conjectures-v2/`. All 100 current v2 files are already correct: the 67
in `deepmind-v2/` on `FormalConjecturesUtil`, the 33 in `conjectures-v2/` on plain
Mathlib, zero on the stale name.

This is what keeps the two directories independent: every file in `conjectures-v2/`
compiles with nothing but Mathlib, and every file in `deepmind-v2/` compiles against
upstream. Neither directory is a mix, so neither needs a per-file check to know how to
build it.

Input selection is already specified in `FABLE_REVIEW_RUN.md:18-25` and is not a choice:
the artifact under review is `deepmind/<N>.lean` when it exists, otherwise
`conjectures/<N>.lean`. The second case is not rare — it is **371 of 1179**, and it is
not evenly spread:

| Batch | Total | has `deepmind/` | no `deepmind/` |
|---|---|---|---|
| 1101–1179 | 79 | 64 | **15** |
| 1–100 | 100 | 56 | **44** |
| 101–200 | 100 | 67 | 33 |
| 201–300 | 100 | 54 | **46** |
| 301–400 | 100 | 46 | **54** |
| 401–500 | 100 | 67 | 33 |
| 501–600 | 100 | 79 | 21 |
| 601–700 | 100 | 83 | 17 |
| 701–800 | 100 | 88 | 12 |
| 801–900 | 100 | 69 | 31 |
| 901–1000 | 100 | 68 | 32 |
| *(1001–1100, done)* | *100* | *67* | *33* |

The 67/33 split of batch 1 was not a universal constant — it ranges from 46/54 to 88/12.
Since the no-`deepmind/` path reviews a raw plain-Mathlib file and judges soundness
rather than style, those problems are somewhat cheaper per unit but produce v2 files that
build locally rather than upstream (see §6).

### One deliberate change from batch 1

In the 1001–1100 run, fixes were applied **in place to `deepmind/<N>.lean`**, and
the v2 set was assembled afterward by copying. **Do not repeat that.** Write fixes only
to the v2 directories and leave `deepmind/` and `conjectures/` immutable.

Rationale: the benchmark's value is the before/after pair. Keeping the "before" side
untouched on disk makes every defect a clean two-file diff instead of something that has
to be excavated from git history, and it means a v3 run re-reads exactly the same inputs
batch 1 saw. It also retires open thread 5 from the synthesis (the 1062/1082 fixes that
exist only in v2 and were never propagated back) — under the new rule, *nothing* is ever
propagated back, by design.

Batch 1's in-place edits stay as they are; they're committed and the git history is
intact. Just don't extend the pattern.

## 4. Batch order

```
1101-1179  (79)   ← next
1-100      (100)
101-200    (100)
201-300    (100)
301-400    (100)
401-500    (100)
501-600    (100)
601-700    (100)
701-800    (100)
801-900    (100)
901-1000   (100)  ← includes promote-only work for 1000
```

11 batches, 1079 problems. One commit per problem, following the existing subject-line
convention (`Fable review <N>: <what changed>`), one branch and PR per batch.

Re-reviewing 1001–1100 with a current model is explicitly **deferred to the end** of the
program. It is the one batch where a second data point would tell us something about
model-over-model improvement, but it costs a full batch to learn, and it is worth more
once the pipeline is stable.

## 5. Concurrency and credit policy

This is the constraint that decides whether the run finishes, so it gets stated first as
a rule and then justified.

> **Rule: at most one *model invocation* in flight at a time by default — one `claude -p`
> review process, or one review subagent. Two is the hard ceiling, and only after a
> metered batch shows headroom. Never more.**
>
> **The rule governs model calls only.** It does not apply to `lake build`, `grep`, or any
> other local computation — those cost CPU, not tokens, and should use the whole machine.
> See §6.

**Why parallelism is the wrong lever.** It does not reduce total tokens — 1079 problems
cost what they cost. It only raises the *rate*, and rate is precisely what the 5-hour
session window and the weekly cap measure. Running two problems at once halves the
wall-clock and doubles the burn rate, arriving at the same limit twice as fast. This is
not theoretical here: `readme.md` already records it from the formalization run — *"I
tried to parallelize the calls but that ended up torching through my per-session limit
too fast, so I fell back on a very basic strategy of just processing the problems one at
a time."* That finding transfers directly, and Fable reviews are far more expensive per
problem than formalizations were.

**Why headless processes beat in-session subagents for this workload.** An orchestrator
that reviews problems as subagents inside one long session accumulates context: every
completed problem's summary stays in the parent's history and is re-sent on every
subsequent turn. Across 100 problems that overhead grows without bound and is pure waste.
A per-problem `claude -p` process starts clean, so cost per problem is roughly constant
and the batch cost is predictable — which is also what makes metering meaningful. The
existing `Makefile` already works this way; keep it.

So: the answer to "limit to 2 subagents" is that the subagent question mostly dissolves.
Use one process per problem, and let `make -j` or a plain loop be the throttle.

**Metering, so the ceiling is data instead of a guess.** Headless runs support
`--output-format json`, which returns a result envelope with usage and cost fields
alongside the text. Append one line per problem to a TSV and the burn rate becomes
observable in real time:

```bash
# review-one.sh <N>
N=$1
[ -f "fable-review/$N.md" ] && exit 0          # idempotent: skip completed work
claude --dangerously-skip-permissions --print --output-format json \
       --model claude-fable-5 --max-turns 200 \
       "Read FABLE_REVIEW_RUN.md. Apply to problem $N. Write the fixed file to deepmind-v2/$N.lean if deepmind/$N.lean exists, otherwise conjectures-v2/$N.lean; do not modify deepmind/ or conjectures/." \
  | tee "run-logs/$N.json" \
  | python3 -c 'import sys,json;d=json.load(sys.stdin);print("'"$N"'",d.get("total_cost_usd"),d.get("num_turns"),d.get("duration_ms"),sep="\t")' \
  >> run-logs/burn.tsv
```

Confirm the exact JSON field names once with a throwaway prompt before trusting the
parse — they are what the harness reports, not a stable contract.

Then the batch is just:

```bash
seq 1101 1179 | xargs -P1 -I{} ./review-one.sh {}
```

`-P1` is the throttle, and what it throttles is *review processes* — each one makes model
calls, so this is the number that spends tokens. Raise to `-P2` only if `burn.tsv` shows
the session window is not being saturated. Add `sleep` between problems if it is — pacing
across the window beats stalling at the cap. Do not confuse this `-P` with the one in the
§6 build commands, which throttles compilers and costs nothing.

**What the model can and cannot monitor mid-session.** Inside a single headless run, the
agent has no view of account-level rate-limit state and cannot self-throttle; do not
design around it being able to. Monitoring belongs to the orchestrator and to you:

- `burn.tsv` above — per-problem cost and duration, the most useful signal, and free.
- `/cost` and `/context` in an interactive session for a spot check.
- `CLAUDE_CODE_ENABLE_TELEMETRY` with an OTEL metrics exporter, if you want a dashboard
  over a multi-day run rather than a text file.

**Runaway guards.** `--max-turns` bounds a single problem that goes pathological.
Idempotence (the `[ -f ]` check) means a killed batch resumes by re-running the same
command — important, since a batch spans days and will get interrupted.

## 6. Compile verification

Reviews run without a compiler by design (`FABLE_REVIEW.md:6-7`), so every fix lands
unverified and the compile pass is a separate step at the end of each batch. Which
environment depends on the file's provenance, per `SETUP_LEAN_ENV.md`:

The directory split makes this mechanical — no per-file inspection, one command each:

```bash
# conjectures-v2/ — plain Mathlib, builds in this repo
lake build ErdosV2                 # the whole set
lake build 'ConjecturesV2.«1003»'  # or one file

# deepmind-v2/ — FormalConjecturesUtil, sibling checkout only
cd /workspaces/formal-conjectures
cp /workspaces/erdos-ai/deepmind-v2/*.lean FormalConjectures/ErdosProblems/
TARGETS=$(ls /workspaces/erdos-ai/deepmind-v2/*.lean | xargs -n1 basename \
          | sed 's#^#FormalConjectures/ErdosProblems/#')
lake build $TARGETS
```

**Builds are free — parallelize them.** The §5 concurrency rule governs model calls and
nothing else. `lake` costs CPU, not tokens, so there is no reason to throttle it: run the
local set at `-P$(nproc)` and hand the entire target list to a single `lake build` for the
sibling set, as above. Each `lake` invocation is internally parallel across cores on top
of that. Measured 2026-08-13 with warm caches: `deepmind-v2/`'s 67 files as one invocation
in **17s** (8110 jobs, 0 errors, 0 warnings), and `lake build ErdosV2` over
`conjectures-v2/`'s 33 in **2s** (2733 jobs, 113 `sorry` warnings, 0 non-sorry). There is
nothing to save by going slower.

Batch 1 found three defect classes this way that no amount of review caught — a type
ascription (1062), an attribute grammar error (1082), and 22 linter violations. Expect
the compile pass to find real errors every batch; budget for a fix cycle after it, and
log what it finds, because *"defects a reviewer missed but a compiler caught"* is one of
the more interesting numbers this project can report.

Two standing hazards: `/workspaces/formal-conjectures` is 108 commits behind upstream
with a dirty tree, and the `cp` above overwrites upstream's styled files. Both are
tracked as open threads; resolve before the sibling checkout is needed for a batch.

## 7. Benchmark instrumentation

Cheap to capture during the run, expensive to reconstruct after. Add to every
`fable-review/<N>.md` a machine-readable header:

```yaml
---
problem: 1103
reviewer_model: claude-fable-5
review_date: 2026-08-14
input_artifact: deepmind/1103.lean   # or conjectures/1103.lean
verdict: NEEDS REVISION              # ACCEPT | ACCEPT WITH NITS | NEEDS REVISION
confidence: medium
source_recovered: true
defects: [wrong-polarity, vacuous-quantifier]
compile_status: pass                 # filled in by the §6 pass
---
```

A controlled vocabulary for `defects` matters more than its initial completeness — start
from the classes batch 1 actually found (wrong polarity, vacuous or trivializing
statement, ℕ subtraction/division traps, `answer()` shape errors, restyling meaning
drift, hallucinated attribution, false page-stated bounds) and extend it as new ones
appear. Backfilling the 101 existing notes is a small, self-contained job that can happen
any time.

The headline metrics fall out: defect rate per model generation, defect-class
distribution, reviewer-vs-compiler catch rates, and — once a v3 run exists — how much of
v2's defect list a newer model independently rediscovers.

## 8. Open decisions

1. **Which model reviews batches 2+.** Batch 1 was Fable 5 throughout. Staying on Fable 5
   keeps the corpus homogeneous and comparable; switching to the strongest current model
   probably improves quality but splits the dataset. Recommendation: hold Fable 5 for the
   whole v1179 sweep, then re-run 1001–1100 with the newer model as the first v3 batch —
   that yields a clean model-over-model comparison on identical inputs instead of a
   corpus that silently changes reviewer partway through.
2. **`CHECKLIST.md` §12 vs reality.** It requires four custom linters that exist only in
   the upstream environment, for files explicitly not destined upstream. Either port the
   linters or scope §12 to the subset it can apply to.
3. **The five real revisions sitting unstaged in `/workspaces/formal-conjectures`**
   (1002, 1057, 1082, 1090, 1096) — net-additive improvements to files upstream already
   has. Contributing them upstream contradicts `FABLE_REVIEW.md:31`. Worth an explicit
   decision rather than leaving them to rot in a dirty tree.
4. ~~**Nothing in this repo's user-authored docs mentions `conjectures-v2`.**~~ —
   addressed 2026-08-13: `readme.md` now has a "Second pass" section describing the
   review and linking here. The `Makefile` still has no rule for it; add one if the
   `review-one.sh` loop in §5 settles into something stable.
