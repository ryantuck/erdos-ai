# Setting up a Lean environment for `lake build`

Two separate toolchains are needed, because the two file collections in this repo
target different repos and different Lean versions:

| Files | Imports | Builds in | Lean |
|---|---|---|---|
| `conjectures/*.lean`, `conjectures-v2/*.lean` | plain `Mathlib.*` | this repo | 4.28.0 (`lean-toolchain`) |
| everything under `deepmind/` | `FormalConjecturesUtil`, `FormalConjecturesForMathlib.*` | `../formal-conjectures` | 4.27.0 |

**Only the first row matters for the live pipeline.** `conjectures/` is the input and
`conjectures-v2/` the output, both plain Mathlib, both building here — so a single
toolchain covers all current work. Section 3 is needed only to read or rebuild the
archived DeepMind effort; see `deepmind/README.md`.

Budget ~15 min and ~13 GB of disk for both. Each Mathlib cache is ~6 GB.

## 1. Install elan (once)

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
export PATH="$HOME/.elan/bin:$PATH"
```

elan reads `lean-toolchain` in whichever directory you run from and fetches that
version on demand, so you never pick a Lean version by hand.

## 2. This repo (`conjectures/`)

```bash
cd /workspaces/erdos-ai
lake exe cache get      # clones the 9 deps at lake-manifest.json revs + ~6 GB of Mathlib oleans
lake build conjectures/13.lean
```

First `cache get` takes ~10 min. After that a single file builds in ~15 s.

- `warning: declaration uses 'sorry'` is expected — these are formalizations, not proofs.
- **Build one file at a time.** A bare `lake build` builds the whole `Erdos` lib,
  i.e. all 1179 files in `conjectures/`; on 8 cores that is a couple of hours.
- `lakefile.toml` globs `conjectures.*` and `ConjecturesV2.*` only. Nothing under
  `deepmind/` is a Lake target here — see section 3.

### Second pass (`conjectures-v2/`)

The plain-Mathlib half of the second pass is its own lib and needs no external
checkout. Unlike `Erdos`, the whole thing is cheap to build at once:

```bash
lake build ErdosV2                 # all 33 files, ~2700 jobs
lake build 'ConjecturesV2.«1003»'  # or one at a time
```

The quotes and guillemets are required — the module name is numeric. `ErdosV2` is out
of `defaultTargets`, so a bare `lake build` still only builds `Erdos`. `ConjecturesV2`
is a symlink to `conjectures-v2/` (Lake globs need a valid identifier and
`conjectures-v2` has a hyphen), and `ConjecturesV2.lean` is the stub root module the
glob requires, mirroring `conjectures.lean`.

## 3. The DeepMind repo (archive only)

**Not needed to run the pipeline.** Everything below concerns the archived work under
`deepmind/`; skip it unless you are rebuilding that.

Those files import `FormalConjecturesUtil`, which only exists upstream. Put a sibling
checkout at `../formal-conjectures`:

```bash
cd /workspaces
git clone --depth 50 https://github.com/google-deepmind/formal-conjectures.git
cd formal-conjectures
lake exe cache get      # its own Lean 4.27.0 + ~6 GB Mathlib cache
```

To build one of our files, copy it into the upstream tree and build by path:

```bash
cd /workspaces/formal-conjectures
cp /workspaces/erdos-ai/deepmind/deepmind-v2/1100.lean FormalConjectures/ErdosProblems/
lake build FormalConjectures/ErdosProblems/1100.lean
```

The first such build also compiles `FormalConjecturesUtil` and
`FormalConjecturesForMathlib` (~2 min). Subsequent files take ~20 s.

Build the whole set at once:

```bash
cd /workspaces/formal-conjectures
cp /workspaces/erdos-ai/deepmind/deepmind-v2/*.lean FormalConjectures/ErdosProblems/
TARGETS=$(ls /workspaces/erdos-ai/deepmind/deepmind-v2/*.lean | xargs -n1 basename \
  | sed 's#^#FormalConjectures/ErdosProblems/#')
lake build $TARGETS
```

Measured 2026-08-13 with a warm cache: all 67 in 17 s (8110 jobs, 0 errors, 0 warnings).
Builds cost CPU, not tokens — parallelize freely.

Copying overwrites upstream files where the problem number already exists. Undo with
`git -C /workspaces/formal-conjectures checkout FormalConjectures/ErdosProblems`.

### Import path drift

`deepmind/deepmind/*.lean` (all 808) use the old upstream path:

```lean
import FormalConjectures.Util.ProblemImports   -- stale; no longer exists
import FormalConjecturesUtil                   -- current
```

Rewrite before building:

```bash
sed -i 's#^import FormalConjectures\.Util\.ProblemImports$#import FormalConjecturesUtil#' FILE
```

`deepmind/deepmind-v2/` already has this applied. `conjectures-v2/` never needed it — those
files import plain `Mathlib.*`, which is now true of every file the pipeline produces.

## Upstream style gotchas

Two things that pass locally but fail upstream, both hit while building the second pass:

- **Attribute grammar.** The problem status is only `open` or `solved`; a formal-proof
  link is a *separate* attribute. `@[category research formally solved using X at "…"]`
  is a parse error. Correct form:
  `@[category research solved, formal_proof using formal_conjectures at "…", AMS 51]`
  (proof kinds: `formal_conjectures`, `lean4`, `other_system`).
- **`linter.style.openClassical`.** A file-level `open Classical` / `open scoped Classical`
  warns, because it hides decidability assumptions in theorem statements. Either drop it
  (often unused) or scope it to the one declaration that needs it with `open Classical in`
  directly above the declaration's docstring. Usually it is a `noncomputable def` calling
  `Finset.filter` on an undecidable predicate.

## Refreshing after a Mathlib bump

If `lakefile.toml`'s mathlib `rev` or `lean-toolchain` changes, run `lake exe cache get`
again before building, or Lake will compile Mathlib from source (hours).
