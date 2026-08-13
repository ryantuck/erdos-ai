# Setting up a Lean environment for `lake build`

Two separate toolchains are needed, because the two file collections in this repo
target different repos and different Lean versions:

| Files | Imports | Builds in | Lean |
|---|---|---|---|
| `conjectures/*.lean` | plain `Mathlib.*` | this repo | 4.28.0 (`lean-toolchain`) |
| `deepmind/*.lean`, `conjectures-v2/*.lean` | `FormalConjecturesUtil`, `FormalConjecturesForMathlib.*` | `../formal-conjectures` | 4.27.0 |

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
- `lakefile.toml` globs `conjectures.*` only. `lake build deepmind/1100.lean` fails with
  `unknown package deepmind` — see below.

## 3. The DeepMind repo (`deepmind/`, `conjectures-v2/`)

These files import `FormalConjecturesUtil`, which only exists upstream. The Makefile
already assumes a sibling checkout at `../formal-conjectures`, so put it there:

```bash
cd /workspaces
git clone --depth 50 https://github.com/google-deepmind/formal-conjectures.git
cd formal-conjectures
lake exe cache get      # its own Lean 4.27.0 + ~6 GB Mathlib cache
```

To build one of our files, copy it into the upstream tree and build by path:

```bash
cd /workspaces/formal-conjectures
cp /workspaces/erdos-ai/conjectures-v2/1100.lean FormalConjectures/ErdosProblems/
lake build FormalConjectures/ErdosProblems/1100.lean
```

The first such build also compiles `FormalConjecturesUtil` and
`FormalConjecturesForMathlib` (~2 min). Subsequent files take ~20 s.

Build the whole set at once:

```bash
cd /workspaces/formal-conjectures
cp /workspaces/erdos-ai/conjectures-v2/*.lean FormalConjectures/ErdosProblems/
TARGETS=$(ls /workspaces/erdos-ai/conjectures-v2/*.lean | xargs -n1 basename \
  | sed 's#^#FormalConjectures/ErdosProblems/#')
lake build $TARGETS
```

Copying overwrites upstream files where the problem number already exists
(39 of the 100 in `conjectures-v2/`). Undo with
`git -C /workspaces/formal-conjectures checkout FormalConjectures/ErdosProblems`.

### Import path drift

`deepmind/*.lean` (all 808) use the old upstream path:

```lean
import FormalConjectures.Util.ProblemImports   -- stale; no longer exists
import FormalConjecturesUtil                   -- current
```

Rewrite before building:

```bash
sed -i 's#^import FormalConjectures\.Util\.ProblemImports$#import FormalConjecturesUtil#' FILE
```

`conjectures-v2/` already has this applied.

## Upstream style gotchas

Two things that pass locally but fail upstream, both hit while building
`conjectures-v2/`:

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
