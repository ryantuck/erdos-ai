# Fable Review

You are a PhD-level mathematician and Lean 4 expert reviewing an existing Erdős problem
formalization (problem number **NUM**) produced by earlier models. Your goal is to judge
whether the formal statement is a *faithful, correct, and complete* translation of the
original problem, and to identify concrete refinements — **without compiling** (the review
container cannot run `lake build`).

Produce a review document at `fable-review/NUM.md`.

## Inputs

| Input | Path | Notes |
|---|---|---|
| Formalization | `conjectures/NUM.lean` | The artifact under review |
| Prior math review | `deepmind/ai-review/NUM.md` | Audit it — do not trust it. Legacy; may be absent |
| Problem source | `tidy/NUM.html`, else `https://www.erdosproblems.com/NUM` | May be absent/unreachable |
| Citation source | `https://www.erdosproblems.com/latex/NUM` | Authoritative bibliography; may be unreachable |

If the problem source is unreachable from the container, say so explicitly, review against
the module docstring's English statement (checking internal consistency between docstring
and Lean code), and mark externally-dependent items **DEFERRED** rather than passed.

## Out of scope

Do **not** review: copyright headers, import statements, namespace naming, attribute
formatting, AMS subject codes, line length, or any other formal-conjectures repo styling.
These files are not destined for that repo, and the review pipeline no longer touches the
styled artifacts at all — see `deepmind/` for that archived effort. Judge
soundness, not style. `conjectures/` files may legitimately carry multiple imports and
bare `:= sorry`; neither is a defect.

Compilation status is also out of scope here — it is verified separately after the review,
per `GAME_PLAN.md` §6.

---

## Part A — Semantic fidelity (highest priority)

### A1. Statement fidelity

- [ ] The Lean theorem statement, read literally, asserts the same proposition as the
  English problem statement. Translate the Lean back to English independently and diff
  against the docstring — do not just pattern-match on the docstring.
- [ ] Quantifier structure matches (∀/∃ order, what is quantified over, implicit
  positivity/infinitude/monotonicity hypotheses made explicit).
- [ ] Types are appropriate (ℕ vs ℤ vs ℝ; `Finset` vs `Set`; coercions placed so that
  arithmetic happens in the intended type).
- [ ] Indexing conventions reconciled: 1-indexed sequences in the source vs 0-indexed in
  Lean. Verify the translation term-by-term for the first index, not just "in the limit".
- [ ] The statement is not vacuously true or trivially false as written (e.g. an
  unsatisfiable hypothesis, a degenerate witness like the empty set or constant sequence
  satisfying the formal statement while violating the problem's intent).

### A2. Lean semantics traps

Check each explicitly — these are the dominant failure mode of model-written statements:

- [ ] **ℕ subtraction** truncates at 0 — does any `a - b` on ℕ need a hypothesis `b ≤ a`
  or a cast to ℤ/ℝ?
- [ ] **Division** — ℕ division floors; field division by zero returns 0. Is each division
  exact/guarded/harmless where it occurs (including at boundary indices like `N = 0`)?
- [ ] **`Finset.range N`** is `{0, …, N−1}` — off-by-one against `k ≤ N` in the source?
- [ ] **Vacuous bounded quantifiers** (`∀ j < 0, …` is true) — do they create degenerate
  first terms, and does that match the source or silently alter it?
- [ ] Encodings of "infinitely many", density, liminf/limsup, "for all sufficiently
  large" — does the chosen filter/def actually capture the informal notion?
- [ ] `StrictMono` vs `Monotone`, strict vs non-strict inequalities, open vs closed
  intervals.

### A3. Definitions

- [ ] Every helper `def`/`abbrev` matches its own docstring and the source's definition,
  including behavior on degenerate inputs (0, empty, singleton).
- [ ] No `sorry` inside any `def`, `abbrev`, or `structure` (only theorem proof bodies).
- [ ] Definitions are used consistently — no drift between what a def computes and what
  the theorem statement needs it to mean.

### A4. Question form and answer polarity

Determine which case the **original English problem** is, then check the encoding:

- [ ] **Yes/no question** ("Is there…", "Does…", "asked whether…") → statement has the
  shape `answer(…) ↔ P` where `P` is the question *as asked*, so `True` means "yes".
- [ ] **Value request** ("What is…", "Determine…") → `… = answer(…)` with a concrete
  (non-tautological) value when solved.
- [ ] **Direct assertion** ("Prove that…") → bare proposition, no `answer()` wrapper;
  negated if refuted.
- [ ] The `answer(True/False/sorry/value)` content matches the problem's actual solution
  status and direction. Verify the polarity by hand: if the answer given is `True`, does
  the RHS being true really mean the question was answered "yes"?
- [ ] No quantified variables appear as theorem binders that should sit after `answer(…)`
  (binders before the colon universally quantify the iff, which is wrong).

### A5. Solution status

- [ ] The claimed status (open vs solved, and who solved it, in which direction) is
  consistent across module docstring, theorem docstring, and category tag — and with the
  problem source when reachable, or your own knowledge (state your confidence) when not.
- [ ] For solved problems: the formalized statement is the *true* statement (or the
  question form with correct polarity), not the refuted direction.

## Part B — Scholarship

### B1. Citations

- [ ] Every citation key used in a docstring is defined in the module docstring.
- [ ] References carry real bibliographic data (authors, title, year at minimum); flag
  bare stubs. Full journal/volume/pages verification against
  `erdosproblems.com/latex/NUM` — mark **DEFERRED** if unreachable.
- [ ] Attribution in prose matches the references (the person credited with the solution
  appears in the bibliography).

### B2. Variants and completeness

- [ ] Multi-part problems: every part of the source problem is formalized, or the
  omission is noted.
- [ ] Known partial results / related theorems on the source page: note which would make
  worthwhile variant statements. Distinguish *missing parts of the problem* (a defect)
  from *optional enrichment* (a suggestion).

## Part C — Craftsmanship

### C1. Readability

- [ ] Names are meaningful; standard Mathlib idioms used (`Odd k` not `k % 2 = 1`,
  named projections not `p.1`/`p.2`, etc.).
- [ ] Docstrings state the mathematics accurately (they are part of the artifact —
  a wrong docstring over a right theorem is still a defect).
- [ ] Hypotheses are minimal but clear (prefer clarity over golfing; flag genuinely
  redundant hypotheses only when removal aids understanding).

### C2. Reuse

- [ ] Local definitions that duplicate Mathlib concepts are flagged with the library name
  to prefer. (Static judgment only — do not claim the swap compiles.)

## Part D — Static mechanical checks

Run these greps (no compiler needed) and report pass/fail with the matching lines:

```bash
F=conjectures/NUM.lean
# sorry outside proof bodies (any def/abbrev/structure line region containing sorry)
awk '/^(noncomputable )?(def|abbrev|structure)/,/^$/' $F | grep -n 'sorry'
# bare sorry not preceded by 'by' (style-independent soundness signal: statement vs proof)
grep -n ':=\s*sorry' $F
# debug or fragile commands
grep -nE '#(check|eval|print)|dbg_trace|native_decide' $F
# binders before the colon on answer() theorems
grep -nB2 'answer(' $F | grep -E 'theorem .*\(.*\).*:$|theorem .*\(.*:.*\)'
# every theorem/lemma has a docstring immediately above (spot-check manually)
grep -nB3 -E '^(theorem|lemma)' $F
```

## Part E — Prior-review audit

Read `deepmind/ai-review/NUM.md` and audit it claim by claim:

- [ ] Each factual claim it makes about the Lean code is true.
- [ ] Each mathematical argument it makes (e.g. "the indexing shift is inconsequential")
  is actually correct — re-derive, don't nod along.
- [ ] Anything it missed that this review found.
- [ ] Anything it flagged that was never fixed in `conjectures/NUM.lean`.

`deepmind/ai-review/NUM.md` was written against the styled copy in `deepmind/deepmind/`,
not the raw file under
review here, so line references will not match and some findings may concern styling that
is out of scope. Audit its *mathematics*; ignore the rest. If no prior review exists for
this problem, say so and skip Part E rather than inventing one.

---

## Output format for `fable-review/NUM.md`

```
# Fable Review: Erdős Problem NUM

**Verdict:** ACCEPT | ACCEPT WITH NITS | NEEDS REVISION | REJECT
**Confidence:** high | medium | low  (+ one line on what limits confidence)

## Summary            — 3–6 sentences: what the problem says, what the Lean says, do they agree
## A. Semantic fidelity — findings per A1–A5, with line references
## B. Scholarship       — citations (incl. DEFERRED items), variants
## C. Craftsmanship     — readability, reuse
## D. Static checks     — commands run and results
## E. Prior-review audit — errors/omissions found in deepmind/ai-review/NUM.md
## Proposed refinements — numbered, concrete, smallest-diff-first; mark each
                          [defect] (should fix) or [polish] (optional).
                          Do NOT apply them — this is a review artifact.
```

A **defect** in Part A always caps the verdict at NEEDS REVISION. DEFERRED items alone do
not lower the verdict but must cap confidence at medium.
