# Formal Conjectures PR Checklist

Every item must pass before a PR is approved. Reviewers: reject if any box is unchecked
without an explicit justification.

Sources: [`formal-conjectures/README.md`](../formal-conjectures/README.md) (Style Guidelines §1–7),
[`AGENTS.md`](../formal-conjectures/AGENTS.md), and the five custom linters in
`FormalConjectures/Util/`.

---

## 1. Copyright Header

- [ ] File begins with the **exact** copyright block (no leading blank line):
  ```
  /-
  Copyright 2026 The Formal Conjectures Authors.

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
- [ ] Year is exactly `2026` (the linter accepts any 4-digit year, but new files must use the current year).

## 2. Import Statement

- [ ] Exactly one import line, immediately after the copyright block (separated by one blank line):
  ```
  import FormalConjectures.Util.ProblemImports
  ```
- [ ] No other imports are present.

## 3. Module Docstring

- [ ] A `/-! ... -/` module docstring appears after the import, separated by one blank line.
- [ ] Starts with a heading: `# Erdos Problem N` (or appropriate title).
- [ ] Contains a `*Reference:*` line with a markdown link to the source, e.g.:
  ```
  *Reference:* [erdosproblems.com/N](https://www.erdosproblems.com/N)
  ```
- [ ] Includes a brief plain-English description of the problem.
- [ ] Optional: bibliography entries for related papers.

## 4. Namespace

- [ ] All declarations are inside a namespace (`namespace ErdosN ... end ErdosN`).
  - Linter `linter.style.namespace` enforces this; error: *"The declaration '...' is not inside a namespace."*
- [ ] Namespace name uses `UpperCamelCase` (e.g., `Erdos42`, not `erdos_42`).
- [ ] `open` / `open scoped` statements appear **before** the namespace block when opening Mathlib namespaces (e.g., `open Filter Nat Real`).

## 5. Custom Definitions

- [ ] Helper `def`, `abbrev`, or `structure` declarations have a LaTeX docstring (`/-- ... -/`).
- [ ] Definitions that involve classical choice or nonconstructive operations are marked `noncomputable`.
- [ ] No `sorry` in definitions (only in theorem proof bodies).
- [ ] Types and Props use `UpperCamelCase` (e.g., `IsCoveringSystem`).
- [ ] Functions returning types use `lowerCamelCase` (e.g., `normalizedPrimeGap`).
- [ ] Use `local notation` for problem-specific notation, scoped inside the namespace.
- [ ] Consider adding `@[category test]` or `@[category API]` sanity checks for new definitions to verify they behave as expected.

## 6. Theorem Statements

- [ ] Benchmark problems use the `theorem` or `lemma` keyword (not `def` or `example`).
- [ ] Main theorem is named `erdos_N` (snake_case, matching the namespace number).
- [ ] Name follows Lean/Mathlib conventions: `snake_case` for terms of Props.
- [ ] Each theorem has both `@[category ...]` and `@[AMS ...]` attributes on the **same attribute line** (e.g., `@[category research open, AMS 11]`).
- [ ] Main theorems and non-obvious variants have a docstring (`/-- ... -/`).
- [ ] Theorem docstrings should ideally reference the source paper(s) (e.g., `[Er95]`, `[AhKh97]`).

### `answer()` usage

The rule depends on how the **original problem is phrased in English**, not how the
Lean code currently looks. There are three cases (per `formal-conjectures` README §6
and AGENTS.md):

**Case 1 — Problem asks a yes/no question** ("Does ...", "Are there ...", "Is it true that ...", "Can ...", "asked whether ..."):

- [ ] The theorem type is `answer(sorry) ↔ P`, where `P` formalizes the question as asked:
  ```lean
  /-- English: "Does P hold?" -/
  theorem erdos_N : answer(sorry) ↔ P := by sorry
  ```
- [ ] If the problem has been solved, replace `answer(sorry)` with `answer(True)` or `answer(False)` accordingly:
  ```lean
  -- Question answered affirmatively:
  theorem erdos_N : answer(True) ↔ P := by sorry
  -- Question answered negatively:
  theorem erdos_N : answer(False) ↔ P := by sorry
  ```
- [ ] The RHS (`P`) formalizes the **question as originally asked**, so that `answer(True)` means "yes" and `answer(False)` means "no" to that question.

**Case 2 — Problem asks for a specific value** ("What is ...", "Find ...", "Determine ..."):

- [ ] The theorem type uses `= answer(sorry)` (or `answer(sorry) =`), where the answer is a concrete value, not `True`/`False`:
  ```lean
  /-- English: "What is the chromatic number of G?" -/
  theorem problem_N : G.chromaticNumber = answer(sorry) := by sorry
  ```
  ```lean
  /-- English: "Which natural numbers satisfy P?" -/
  theorem problem_N : {n : ℕ | P n} = answer(sorry) := by sorry
  ```
- [ ] When solved, replace `answer(sorry)` with the concrete answer value (e.g., `answer(7)`).
- [ ] Note: providing a trivial or tautological answer (e.g., `{n : ℕ | P n}` itself) does not constitute solving the problem. Whether an answer is mathematically meaningful is outside the scope of the repository.

**Case 3 — Problem is stated as a direct assertion** ("P holds", "Show that ...", "Prove that ..."):

- [ ] The theorem type is `P` directly (no `answer()` wrapper):
  ```lean
  /-- English: "P holds" -/
  theorem erdos_N : P := by sorry
  ```
- [ ] If the problem has been solved to the negative, replace `P` with `¬ P`:
  ```lean
  theorem erdos_N : ¬ P := by sorry
  ```

**Common rules for all cases with `answer()`:**

- [ ] Quantifiers go **after** `answer(sorry)`, not as theorem parameters:
  - Correct: `theorem erdos_N : answer(sorry) ↔ ∀ n, P n`
  - Wrong: `theorem erdos_N (n : ℕ) : answer(sorry) ↔ P n`
  - Linter `linter.style.answer_attribute` enforces this.

**How to decide which case applies:** Read the problem's English description (module docstring, theorem docstring, or source reference). If it asks a yes/no question — "asked whether", "is it true that", "does there exist", "can one" — use Case 1. If it asks for a specific value — "what is", "find the minimum", "determine" — use Case 2. If it asserts a fact — "prove that", "show that", a direct inequality or bound — use Case 3.

## 7. Category Attribute

- [ ] Every `theorem`, `lemma`, and `example` has **exactly one** `@[category ...]`.
  - Linter `linter.style.category_attribute` enforces this.
  - Missing: *"Missing problem category attribute"*
  - Duplicate: *"Duplicate category attribute. There should be only one category attribute per declaration"*
- [ ] The value is one of the following (no others are valid):
  | Category | When to use |
  |---|---|
  | `high_school` | Solvable at high-school level |
  | `undergraduate` | Undergraduate-level |
  | `graduate` | Graduate-level |
  | `research open` | Open research problem |
  | `research solved` | Solved but not formally verified |
  | `research formally solved using <kind> at "<link>"` | Formally verified (`<kind>`: `formal_conjectures`, `lean4`, `other_system`) |
  | `test` | Test declaration |
  | `API` | API declaration |
- [ ] A `research open` theorem must contain `sorry` in its proof body.
  - Linter warns: *"If a problem has a sorry-free proof, it should not be categorised as `open`."*

## 8. AMS Attribute

- [ ] Every `theorem`, `lemma`, and `example` has **exactly one** `@[AMS ...]` attribute (not multiple separate `@[AMS]` tags).
  - Linter `linter.style.ams_attribute` enforces this.
  - Missing: *"Missing AMS attribute."*
  - Multiple: *"The AMS tag should be formatted as AMS 1 3 rather than AMS 1, AMS 3"*
- [ ] At least one AMS subject number is listed.
  - *"The AMS tag should have at least one subject number."*
- [ ] Numbers are in **ascending numeric order**.
  - *"The AMS tags should be ordered as AMS ..."*
- [ ] No duplicate numbers.
  - *"AMS tags contain duplicates. This should be AMS ..."*
- [ ] Every number is a valid AMS MSC2020 code. Valid codes:
  ```
  0  1  3  5  6  8  11 12 13 14 15 16 17 18 19 20
  22 26 28 30 31 32 33 34 35 37 39 40 41 42 43 44
  45 46 47 49 51 52 53 54 55 57 58 60 62 65 68 70
  74 76 78 80 81 82 83 85 86 90 91 92 93 94 97
  ```

## 9. Proof Bodies

- [ ] Open conjectures use `by sorry` (not bare `sorry` or `by { sorry }`).
  ```lean
  theorem erdos_N : ... := by sorry
  ```
- [ ] Multi-line proofs with `sorry` are acceptable when intermediate structure is needed:
  ```lean
  theorem erdos_N : ... := by
    sorry
  ```
- [ ] No `sorry` appears in `def`, `abbrev`, or `structure` declarations.
- [ ] No `sorry` in any file under `FormalConjecturesForMathlib/`.
- [ ] Do **not** include informal proof sketches for open research problems.
- [ ] Avoid `native_decide`.

## 10. Variants & Multi-part Problems

- [ ] Variants are named `erdos_N.variants.<descriptor>` (e.g., `erdos_1.variants.weaker`).
- [ ] All variants live in the **same file** as the main theorem.
- [ ] Each variant has its own `@[category ..., AMS ...]` attributes (they may differ from the main theorem).
- [ ] Variants that strengthen/weaken the main conjecture are documented with a brief docstring.

## 11. Code Quality

- [ ] 2-space indentation throughout.
- [ ] Unicode math symbols used where applicable (`∀`, `∃`, `∈`, `⊆`, `∧`, `∨`, `¬`, `↔`, `→`, `ℕ`, `ℤ`, `ℝ`, `ℂ`).
- [ ] No debug code (`#check`, `#eval`, `#print`, `dbg_trace`).
- [ ] No `set_option` that disables linters (e.g., `set_option linter.style.copyright false`) unless justified.
- [ ] Lines are reasonably short (aim for <100 characters; break long lines).
- [ ] File ends with a single trailing newline.

## 12. Build Verification

- [ ] `lake build` completes with **zero errors** (warnings from `sorry` in open problems are expected and acceptable).
- [ ] All five custom linters pass:
  - `linter.style.copyright`
  - `linter.style.category_attribute`
  - `linter.style.ams_attribute`
  - `linter.style.answer_attribute`
  - `linter.style.namespace`
