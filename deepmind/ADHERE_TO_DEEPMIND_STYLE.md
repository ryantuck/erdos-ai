---
name: formalize-erdos
description: Copy and reformat an Erdős conjecture file from conjectures/<N>.lean into deepmind/<N>.lean, applying all AGENTS.md conventions.
user-invocable: true
---

The user has invoked this skill with an Erdős problem number (e.g. `/formalize-erdos 42`).
Extract the problem number N from the arguments.

Follow these steps exactly:

## Step 1 — Read source and reference files

Read ALL of these files in parallel:
- `conjectures/<N>.lean` — the source file to transform
- `../formal-conjectures/FormalConjectures/ErdosProblems/1.lean` — a reference for the expected style
- `../formal-conjectures/AGENTS.md` — authoritative conventions (re-read every time, do not rely on memory)

Also check whether `deepmind/<N>.lean` already exists. If it does,
tell the user and stop — do not overwrite existing work.

## Step 2 — Determine the category and `answer()` usage

### 2a. Category

Choose exactly one of the following for each theorem/lemma:

- `@[category research open, AMS ...]` — the problem has no accepted solution
- `@[category research solved, AMS ...]` — informally proved, widely accepted
- `@[category research formally solved using <kind> at "<link>", AMS ...]` — a machine-checked
  proof exists; `<kind>` is one of `formal_conjectures`, `lean4`, or `other_system`
- `@[category undergraduate, AMS ...]` — undergraduate-level result
- `@[category high_school, AMS ...]` — high-school-level result
- `@[category graduate, AMS ...]` — graduate-level result
- `@[category test, AMS ...]` — sanity check or unit test for a definition
- `@[category API]` — basic theory lemma around a new definition (no AMS needed)

**Each theorem and lemma gets its own category independently.** A variant may be
`research solved` even if the main conjecture is `research open`.

### 2b. AMS subject(s)

Choose from the table in AGENTS.md. Common choices:
- Number theory (primes, congruences, Diophantine) → `11`
- Combinatorics, graph theory → `5`
- Real/complex analysis → `26` or `30`
- Probability → `60`
Multiple subjects are allowed: `AMS 5 11`.

### 2c. `answer()` elaborator

For any theorem that encodes a **yes/no question** (e.g. "Does X exist?", "Is it true that Y?"),
prefer the `answer()` form over a bare assertion:

```lean
/-- Does $P$ hold? -/
@[category research open, AMS 11]
theorem erdos_N : answer(sorry) ↔ SomeProperty := by
  sorry
```

- If the answer is **unknown**, use `answer(sorry)`.
- If the answer is **known to be yes** (proved), use `answer(True)`.
- If the answer is **known to be no** (disproved), use `answer(False)`.
- The quantification must go *after* `answer(...)`, not before:
  ```lean
  -- CORRECT
  theorem foo : answer(sorry) ↔ ∀ n, P n := by sorry
  -- WRONG
  theorem foo (n : ℕ) : answer(sorry) ↔ P n := by sorry
  ```
- Do **not** use `answer()` for theorems that are direct positive assertions (e.g., asymptotic
  bounds, existence results that are already stated as the true direction of a conjecture
  rather than as a question).

## Step 3 — Write the output file

Write `deepmind/<N>.lean` with the following transformations applied:

### 3.1 Copyright header

Prepend exactly (use the current calendar year in place of YYYY):
```
/-
Copyright YYYY The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
```

### 3.2 Import

Replace all `import` lines with a single line:
```
import FormalConjectures.Util.ProblemImports
```

### 3.3 Module docstring

Add immediately after the import:
```
/-!
# Erdős Problem <N>

*Reference:* [erdosproblems.com/<N>](https://www.erdosproblems.com/<N>)
-/
```
If the source file's top-level docstring contains bibliographic entries (e.g. `[Er55c]` citations)
that are referenced from theorem docstrings, move them into the module docstring so all
references are consolidated there.

### 3.4 `open` and `open scoped` statements

Preserve any `open` and `open scoped` statements that are needed for the declarations.
Place them after the module docstring, before the namespace. Remove any that are made
redundant by `FormalConjectures.Util.ProblemImports`.

### 3.5 Namespace

Wrap all declarations (including `open` lines, if they are specific to the namespace)
in `namespace Erdos<N> ... end Erdos<N>`.

### 3.6 Category and AMS attributes

Add `@[category ..., AMS ...]` immediately before each theorem or lemma that does not
already have one. Use Step 2 to choose the correct value per theorem.

### 3.7 Theorem names

- Rename the primary theorem to `erdos_<N>`.
- Rename variants to `erdos_<N>.variants.<description>` following the pattern in `1.lean`.
- Follow Mathlib naming conventions: theorem names in `snake_case`.

### 3.8 `sorry` style

Replace bare `sorry` with `by sorry` in all theorem bodies.

### 3.9 Docstring math

- Convert inline backtick math like `` `n ≡ a (mod m)` `` to LaTeX `$n \equiv a \pmod{m}$`.
- Convert display math to `$$...$$` blocks where appropriate.
- All mathematical expressions in docstrings should use LaTeX, not Unicode-only notation.

### 3.10 `def` definitions

- Keep all helper definitions.
- Ensure their docstrings use LaTeX math.
- Do **not** add `@[category]` attributes to `def`s — only to `theorem`s and `lemma`s.
- Dissolve `noncomputable section ... end` blocks: instead, mark individual `def`s as
  `noncomputable` where required (i.e. when they involve `ℝ`, `ℂ`, or other non-computable types).

### 3.11 References in theorem docstrings

Each main theorem or lemma docstring should contain a reference if one is available
(e.g. citation keys from the source docstring). Ensure these keys are also explained or
listed in the module docstring.

## Step 4 — Report

After writing the file, briefly summarize:
- The file path written (`deepmind/<N>.lean`)
- The category assigned to each theorem and why
- The AMS subject(s) chosen and why
- Whether `answer()` was used and why (or why not)
- Any other judgment calls made
