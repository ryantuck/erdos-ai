# Session 6 — `9227ed25-1ac5-4cad-8da9-42925153d154`
**Aug 12, 20:07 · 497 KB · most recent work session (ended ~3 h before this one)**
**Theme: how to build v2 here → upstream drift check → Makefile/pipeline explainer → premise corrections → make the 33 Mathlib-only files build in *this* repo. Left changes on disk.**

## Prompts, in order
1. "how do i run lake build conjectures-v2 in this repo"
2. "is this on latest from remote master"
3. "ls ../formal-conjectures" / "show the output"
4. (several `!` bash inputs: `ls .`, `ls -d */`, `ls conjectures | wc -l`)
5. "check the makefile and readme - how does that get assembled"
6. "does this goal make sense - there are 1179 conjectures in conjectures/ that can act as a starting point. Want them pipelined through a fable review into conjectures-v2. that was already occurring i believe for ones that were only in conjectures but weren't in deepmind. confirm there are 1179 … and relay back how many are in conjectures-v2"
7. "for the set that was in the deepmind repo - list them out that were copied to conjectures-v2"
8. "how to execute lake build?" → `!lake build conjectures-v2/1000.lean` (failed) → `!lake build conjectures/1000.lean`
9. "i want to build conjectures-v2/1001.lean"
10. "i want to enable running lake build directly on the files in conjectures-v2" → **interrupted**
11. "i don't want to bring anything from deepmind stuff over. build the ones that don't require it."

## Answers given

### Why `lake build conjectures-v2/…` fails here
Two independent blockers: `lakefile.toml:8` globs `conjectures.*` only (no such package), and the v2 files import `FormalConjecturesUtil` / `FormalConjecturesForMathlib.*`, which exist only upstream on Lean 4.27.0 (this repo is 4.28.0). Demonstrated live by the user's own `!lake build conjectures-v2/1000.lean` → `error: unknown package conjectures-v2` (also noted 1000 isn't in v2 at all; the range is 1001–1100, while `fable-review/` has 101 docs because it includes 1000).

### Upstream drift (new, important)
- **`/workspaces/erdos-ai`: current.** HEAD `427b3002` == `origin/master`, 0 ahead / 0 behind after fetch.
- **`/workspaces/formal-conjectures`: 108 commits behind `origin/main`** — local `539fb16`, upstream `c9052e8`.
- Toolchain/Mathlib unaffected — both sides `v4.27.0`, same Mathlib rev `a3a10db`, so updating wouldn't invalidate the ~6 GB cache.
- Those 108 commits touch 109 files in `ErdosProblems/`, **16 colliding with `conjectures-v2/`**: `1007, 1008, 1014, 1022, 1023, 1026, 1028, 1034, 1036, 1037, 1044, 1047, 1048, 1064, 1071, 1098`. A plain `git pull` there will conflict (working tree is dirty by design: 38 modified + 62 untracked).

### The Makefile pipeline, explained
Four chained pattern rules — asking for the last pulls the whole chain:
```
html/%.html      : curl erdosproblems.com/%
tidy/%.html      : htmlq .problem-box --pretty
conjectures/%.lean : claude -p "read FORMALIZE_CONJECTURE.md. Formalize conjecture number %"
deepmind/%.lean  : claude -p "read ADHERE_TO_DEEPMIND_STYLE_GUIDE.md. Apply to problem %"
build-logs/%.txt : lake build conjectures/%.lean | tee
```
Plus a set-arithmetic layer of `comm`/`cat` rules over `all-conjectures.txt` (= `seq 1 1179`), `completed-`, `stylized-`, `deepmind-`, `todo-`, `to-stylize.txt` deciding which problems get fed in. Notes: `make setup` doesn't create `deepmind/`; `make set-path` can't work (each recipe line is its own subshell) — which is why `SETUP_LEAN_ENV.md` says to edit `~/.bashrc`.

### Two corrections to the user's stated goal
1. **`conjectures/` isn't what the Fable review consumes.** `FABLE_REVIEW.md` names `deepmind/NUM.lean` as "the artifact under review"; `conjectures/NUM.lean` is only a cross-check that nothing was lost in restyling. All 67 v2 files with a `deepmind/` counterpart **differ from it** (genuinely revised) and none derive from `conjectures/`. Sample 1007: `conjectures/` 2066 B plain Mathlib, `deepmind/` 5033 B, `conjectures-v2/` 5017 B with `import FormalConjecturesUtil`.
2. **"It ran on the ones in conjectures but not deepmind" is backwards.** 67 of the 100 *are* in `deepmind/`. Selection was a contiguous numeric range — `fable-review/` = 1000–1100 (101 docs), v2 = 1001–1100.
- Counts confirmed: `conjectures/` = **1179** `.lean`; `conjectures-v2/` = **100**, exactly 1001–1100 contiguous.

### The 67 vs 33, enumerated
**67 with a local `deepmind/` source** (all differ from it — each was revised):
`1001 1002 1005 1006 1007 1008 1009 1010 1011 1012 1013 1014 1015 1016 1017 1018 1019 1020 1021 1022 1023 1024 1025 1026 1027 1028 1029 1030 1031 1032 1033 1034 1035 1036 1037 1039 1040 1042 1044 1045 1046 1047 1048 1050 1053 1057 1058 1066 1069 1070 1075 1076 1078 1079 1081 1082 1083 1086 1087 1088 1089 1090 1091 1096 1098 1099 1100`

**52 that exist in upstream `origin/main`** (a different set):
`1002 1003 1004 1007 1008 1014 1022 1023 1026 1028 1034 1036 1037 1038 1041 1043 1044 1047 1048 1049 1051 1052 1054 1055 1056 1057 1059 1060 1061 1062 1063 1064 1065 1067 1068 1071 1072 1073 1074 1077 1080 1082 1084 1085 1090 1092 1093 1094 1095 1096 1097 1098`

**Key insight that fell out**: **all 33** v2 files lacking a `deepmind/` version are already upstream — a perfect match, not partial. The styling pass deliberately skipped problems DeepMind had already formalized, which is *why* those 33 have no `deepmind/` file.

### Builds run
- `FormalConjectures/ErdosProblems/1003.lean` upstream → 1256 jobs, ~70 s.
- User's `!lake build conjectures/1000.lean` → exit 0, 1201 jobs, 105 s, expected `sorry` warning at line 43.
- `1001.lean` upstream → 8044 jobs, 20 s, no warnings (faster: `FormalConjecturesUtil` warm).

### The deliverable: local builds without the sibling repo
First attempt (a separate `v2/` package symlinking into `/workspaces/formal-conjectures/.lake/packages`) was **interrupted by the user** — "i don't want to bring anything from deepmind stuff over" — and torn down (`rm -rf v2`).

Second approach, kept: wire `conjectures-v2` into **this** repo's lakefile on Lean 4.28 / its own Mathlib, no upstream dependency.
- Two Lake obstacles: globs must be valid identifiers, so `globs = ["«conjectures-v2».*"]` is a parse error → worked around with a root symlink `ConjecturesV2 → conjectures-v2`. And Lake won't resolve the `path/to/file.lean` target form through a symlinked dir — only the module-name form works.
- **The command:** `lake build 'ConjecturesV2.«1003»'` (quotes required — numeric module name needs guillemets).
- **All 33 Mathlib-only files built — 0 failures**: `1003 1004 1038 1041 1043 1049 1051 1052 1054 1055 1056 1059 1060 1061 1062 1063 1064 1065 1067 1068 1071 1072 1073 1074 1077 1080 1084 1085 1092 1093 1094 1095 1097`. Mostly 2–4 s warm; slowest 1004 (37 s) and 1038 (35 s). 113 `sorry` warnings total, every file ≥1 — expected.
- The 7 pre-flagged as likely failures all passed: their `answer(…)` / `@[category …]` hits are **inside docstring prose**, not syntax (e.g. `1043.lean:37` is a backticked sentence; 1062/1097 mention `answer(sorry)` describing the upstream form).
- The 33 Mathlib-only files are **exactly** the 33 with no `deepmind/` counterpart — three independent groupings that keep landing on the same set.

## State left on disk (still present now)
- `lakefile.toml` — **tracked edit**: new `[[lean_lib]] name = "ErdosV2"`, `srcDir = "."`, `globs = ["ConjecturesV2.*"]`, deliberately **not** in `defaultTargets` so a bare `lake build` still only builds `Erdos`. Comment block explains the symlink and the sibling-repo caveat.
- `ConjecturesV2` — untracked root symlink → `conjectures-v2`.
- Revert with `git checkout lakefile.toml && rm ConjecturesV2`.

## Explicit ceiling stated
This covers **33 of 100**. The other 67 import `FormalConjecturesUtil` and still require `/workspaces/formal-conjectures`; there's no way to build them here without vendoring that library, since it defines `@[category …]`, `answer(…)`, and the AMS attributes.
