# Synthesis — eight sessions on `/workspaces/erdos-ai`

> **Superseded in part.** Written mid-session-8, before that session redefined the
> pipeline and archived the DeepMind effort. The history and the process lessons still
> hold; anything about directory layout, the 67/33 split, or open threads is stale — read
> `08-0d3a5042-pipeline-restructure.md` and `../../GAME_PLAN.md` for current state.

*Aug 4 → Aug 13, 2026. Sources: `01`–`06` docs in this directory, verified against disk on Aug 13. Updated Aug 13 ~18:20 by session 8.*

## One-line story
Two Aug 4 sessions built a Lean 4 environment and produced `conjectures-v2/` (Erdős problems 1001–1100, compiling clean). The four Aug 12 sessions **produced almost no new artifacts** — they spent their budget re-deriving what Aug 4 already knew, because nothing durable carried between them. Aug 13 closed the loop: session 7 wrote the first durable memories, session 8 committed the nine-day-old work and opened PR #3.

## Timeline

| # | ID | When | Duration/size | Net new output |
|---|---|---|---|---|
| 1 | `2ff30151` | Aug 4 15:44 | 563 KB | **Everything**: elan + 2 toolchains, upstream clone, `conjectures-v2/` (100 files), 26 file fixes, all 100 building clean, `SETUP_LEAN_ENV.md` |
| 2 | `6d584690` | Aug 4 16:43 | 57 KB | None — killed mid-tool-call while parsing session 1's transcript |
| 3 | `8ef14022` | Aug 12 13:21 | 285 KB | Provenance audit (correct); two wrong conclusions |
| 4 | `ec75be9c` | Aug 12 16:33 | 236 KB | Corrected session 3; re-ran full build (clean); ended before reporting it |
| 5 | `01410245` | Aug 12 17:35 | 179 KB | Re-ran the build *again* (session 4's log had been reaped from `/tmp`); style-gap table |
| 6 | `9227ed25` | Aug 12 20:07 | 497 KB | **`lakefile.toml` + `ConjecturesV2` symlink → 33 files build in this repo**; upstream-drift finding; Makefile explainer |
| 7 | `7e577b95` | Aug 13 17:14 | 731 KB | This synthesis + the `01`–`06` docs; **the first durable memories** — 3 `project` memories + `MEMORY.md` |
| 8 | `0d3a5042` | Aug 13 | — | **Six merged PRs (#3–#8).** Committed the Aug 4 work; wrote `GAME_PLAN.md`; **redefined the pipeline**; archived DeepMind. See `08-…` — it supersedes much of this document |

Sessions 2, 4, and 5 each ended mid-turn or on an unanswered question.

## The one number that keeps recurring: 67 / 33

Five independent groupings land on the **same partition** of the 100 files:

| | 67 | 33 |
|---|---|---|
| Source dir | `deepmind/<N>.lean` | `conjectures/<N>.lean` |
| Apache copyright header | ✅ | ❌ |
| Import | `FormalConjecturesUtil` | plain `Mathlib.*` |
| `@[category …]` attributes | ✅ | ❌ |
| Already formalized upstream | — | ✅ **all 33** |
| Builds in `erdos-ai` | ❌ | ✅ |

The causal chain: the DeepMind styling pass deliberately skipped problems upstream had already formalized → those 33 never got a `deepmind/` file → they stayed plain-Mathlib → which is exactly why they're the only ones that build locally.

**The 33:** `1003 1004 1038 1041 1043 1049 1051 1052 1054 1055 1056 1059 1060 1061 1062 1063 1064 1065 1067 1068 1071 1072 1073 1074 1077 1080 1084 1085 1092 1093 1094 1095 1097`

## Verified current state (Aug 13)

- `conjectures/` **1179** · `deepmind/` **808** · `fable-review/` **101** (1000–1100) · `conjectures-v2/` **100** (1001–1100)
- `erdos-ai` on `master` at **`3ee652c8`**, clean. Top level 33 entries. *(Was `427b3002` when this document was written; six PRs merged since.)*
- `/workspaces/formal-conjectures` at `539fb16`, Lean 4.27.0, 7.3 GB `.lake`, working tree 38 M + 62 ??
- Memory dir `~/.claude/projects/-workspaces-erdos-ai/memory/` — **populated as of Aug 13 16:52** (`conjectures-v2-state`, `lean-build-two-environments`, `erdos-ai-open-threads`, + `MEMORY.md`). It was empty when sessions 2–5 checked it.

## Build status — settled, three times over

`conjectures-v2/` compiles green. Confirmed on Aug 4 (`8143 jobs`, 0 errors, 0 warnings after wiping the build dir), re-confirmed Aug 12 16:31 with artifacts deleted for a genuine recompile, and again Aug 12 17:35. Separately, the 33 Mathlib-only files build in `erdos-ai` itself with 0 failures (113 `sorry` warnings, expected).

Three defect classes were found and fixed, all compiler-driven:
1. `1062` — `∀ᶠ n in Filter.atTop` elaborated `n : ℝ`; needs `∀ᶠ (n : ℕ)`.
2. `1082` — `@[category research formally solved using …]` is a parse error; status word must be `open` or `solved`, with `formal_proof using …` as a separate attribute.
3. 22 files — `linter.style.openClassical`: 10 didn't need `Classical` at all, 12 needed it narrowed to `open Classical in` before one declaration.

Fixes 1 and 2 exist **only in `conjectures-v2/`** — `conjectures/1062.lean` and `deepmind/1082.lean` still carry the defects.

## Where sessions contradicted each other

| Claim | By | Corrected by |
|---|---|---|
| "The v2 fix pass was never verified by a build" | 3 | 4 — oleans from Aug 4 15:14–15:16 prove it was; session 3 only looked at `build-logs/` |
| "The 33 unstyled files won't build against `../formal-conjectures` at all" | 3 | 4, 6 — they build fine; the gap is style/conformance only |
| "The 24 edits were hand edits" | 3 | 4 — they were compiler-driven insert-recompile-repeat |
| "Fable credits ran out ~1080" | user | 3 — all 101 review commits exist, full-length through 1100.md |
| "v2 was fed from `conjectures/` for problems not in `deepmind/`" | user | 6 — backwards; 67 of 100 came *from* `deepmind/`, and `FABLE_REVIEW.md` names `deepmind/` as the artifact under review |

Every wrong claim came from a session reconstructing history from disk with no handoff. Session 3 wasn't careless — it was blind.

## The meta-problem

Four of six sessions opened by hand-parsing a predecessor's `.jsonl` with ad-hoc `jq`/`python3`. Session 5 had to redo an entire build purely because session 4's log lived in `/tmp` and got reaped. The memory directory was checked four separate times and was empty every time. That is the single highest-leverage fix available here — a `MEMORY.md` plus a handful of `project` memories would have saved most of Aug 12.

**Fixed in session 7**, which wrote three `project` memories and the index. Session 8 confirmed they work: it opened with the state already in context and went straight to committing, no transcript archaeology.

**But the lesson repeated once more.** These seven docs were written to session 7's *scratchpad* — `/tmp/claude-1000/…/7e577b95-…/scratchpad/sessions/` — and that directory was reaped within the hour. Session 8 had to reconstruct all seven from the `Write`/`Edit` tool inputs in session 7's `.jsonl`, i.e. exactly the archaeology this document criticizes. The memories survived because they live under `~/.claude/`, not `/tmp`. **Corollary: `/tmp` is not storage.** Anything meant to outlive a session belongs in the memory dir or in the repo.

## What the pipeline docs actually say (checked Aug 13)

`conjectures-v2` is **not mentioned in any user-authored doc** — not `readme.md`, not the `Makefile`, not the workflow docs. It appears only in `SETUP_LEAN_ENV.md` and the `lakefile.toml` comment, both written by Claude in these sessions. Until Aug 13 it had never appeared in git history either; `25712b4e` and PR #3 are now the first record of it, but no *user-authored* doc describes it. The goal still exists purely as session prompts.

The *need* for it is documented, though:

| Doc | Line | Says |
|---|---|---|
| `FABLE_REVIEW.md` | 6–7 | reviews run "**without compiling** (the review container cannot run `lake build`)" |
| `FABLE_REVIEW.md` | 31 | "Compilation status is also out of scope." |
| `CHECKLIST.md` | §12 | `lake build` must complete with zero errors + five custom linters |
| `FIX_REVIEW_ISSUES.md` | 105 | verify with `lake build FormalConjectures/ErdosProblems/NUM.lean` |

So compilation is deliberately deferred by the review pipeline and required by the checklist — this box is where that deferred step got done.

**Two doc findings that retire open threads:**
- `FABLE_REVIEW.md:31` — "These files are **not destined for that repo**." The restyle-for-upstream thread was off-goal.
- `FABLE_REVIEW_RUN.md` already handles the no-`deepmind/`-file case (exactly the 33): note that the authoritative artifact lives upstream, and "raw files may legitimately have multiple imports and bare `:= sorry` — **judge soundness, not style**."

Residual contradiction: `CHECKLIST.md` §12 requires the four custom linters (`copyright`, `category_attribute`, `ams_attribute`, `answer_attribute`), which exist only in the upstream environment — unsatisfiable for files explicitly not destined for upstream.

## The working trees

**`erdos-ai`** — **committed Aug 13**, after 9 days. `25712b4e` on branch `conjectures-v2`: 104 files, +12230, comprising the `lakefile.toml` `ErdosV2` lib (10 lines, out of `defaultTargets` so it can't affect existing builds), the `ConjecturesV2` symlink, `SETUP_LEAN_ENV.md` (113 lines), and `conjectures-v2/` (100 files). Pushed, and open as **PR #3 → `master`**. Working tree clean.

**`/workspaces/formal-conjectures`** — 38 M + 62 ??, and the 38 split two ways, which no session had separated:
- **33 are the known style regressions** — exactly the raw-style set; our plain-Mathlib copies clobbering upstream's styled files. Pure noise, should be reverted.
- **5 are genuine content revisions** — `1002 1057 1082 1090 1096`: styled files where the Fable-reviewed version differs from upstream's. Net-additive (+72/−31, +102/−50, +48/−5, +42/−12, +96/−19) — added variants, citations, corrected statuses. All five are **unchanged upstream since local HEAD**, so the diffs are still current despite the 108-commit lag.
- The 62 untracked are v2 problems with no upstream counterpart.

Those 5 diffs plus the 62 new files are the only remaining PR-shaped material — and they'd target *upstream*, squarely against `FABLE_REVIEW.md:31`, which says these files aren't destined there. Worth an explicit decision rather than drift. (PR #3 is against this repo's own `master`, so it doesn't touch that question.)

## Open threads, in priority order

1. ~~**The 67-file restyle**~~ — **retired.** `FABLE_REVIEW.md:31` and `FABLE_REVIEW_RUN.md` both say these files aren't destined for upstream and raw style is acceptable for the 33. Sessions 3–5 offered work the pipeline docs don't want.
2. **Upstream is 108 commits behind** (`539fb16` vs `c9052e8`), with **16 problems colliding** with `conjectures-v2/`: `1007 1008 1014 1022 1023 1026 1028 1034 1036 1037 1044 1047 1048 1064 1071 1098`. Toolchain and Mathlib rev are unchanged, so pulling won't cost the 6 GB cache — but the dirty tree will conflict.
3. **33 regressions in the upstream working tree** — the `cp` overwrote upstream's styled files with plain-Mathlib versions. Known, harmless locally, reversible via `git -C /workspaces/formal-conjectures checkout FormalConjectures/ErdosProblems` (which also discards all 38 modifications).
4. ~~**Nothing is committed.**~~ — **done Aug 13.** All of it landed as `25712b4e` and is open as PR #3. Only thing left: review and merge.
5. **The 1062/1082 fixes were never propagated** back to `conjectures/` and `deepmind/`.
6. **The user's stated goal** — pipeline all 1179 through Fable review into v2 — was corrected on its premises but never re-planned. At 100 problems per ~2-day cycle, 1179 is ~12× the work done so far, and the input should be `deepmind/` (808 files), not `conjectures/`.

## Commands worth keeping

```bash
# 33 Mathlib-only files, in this repo (quotes + guillemets required)
cd /workspaces/erdos-ai && lake build 'ConjecturesV2.«1003»'

# anything importing FormalConjecturesUtil — sibling repo only
cd /workspaces/formal-conjectures && lake build FormalConjectures/ErdosProblems/1001.lean

# all 100
cd /workspaces/formal-conjectures
cp /workspaces/erdos-ai/conjectures-v2/*.lean FormalConjectures/ErdosProblems/
TARGETS=$(ls /workspaces/erdos-ai/conjectures-v2/*.lean | xargs -n1 basename | sed 's#^#FormalConjectures/ErdosProblems/#')
lake build $TARGETS
```
