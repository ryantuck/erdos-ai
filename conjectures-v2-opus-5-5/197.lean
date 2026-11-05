-- [AI - Claude Opus 5.5]: Erdős Problem 197 — second-pass formalization
import Mathlib.Data.Set.Function
import Mathlib.Order.Disjoint

open Set Function

/-!
# Erdős Problem #197

*Source:* [erdosproblems.com/197](https://www.erdosproblems.com/197) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; captured 2026-03-05). [ErGr79] [ErGr80]

Can $\mathbb{N}$ be partitioned into two sets, each of which can be permuted to avoid monotone
3-term arithmetic progressions?

Remarks recorded on the page: if three sets are allowed then this is possible.

## The defect and its fix

"Monotone" means increasing **or decreasing** (as in Problems 194–196). The input's
`HasMonotone3TermAP` counts only increasing progressions, so its "avoid" condition is weaker, and
its statement is much weaker than the page's question. It is in fact elementary. Let
$t_m=3^m-1$; give $[t_m,t_{m+1})$ to the first set for even $m$ and to the second for odd $m$, and
list each set block by block, increasing between blocks and decreasing within a block. An increasing
3-term progression $x<y<z$ must use three different blocks, and then $z\ge t_{m+2}>2y$, so
$z\ne2y-x$. (This argument is not formalized here.)

v2 defines the two-sided notion (`HasMonotone3TermAP197`, `CanPermuteToAvoid197`) and states the
question with it, in the "yes" direction (OPEN). The input's statement is kept as
`variants.first_pass`, and v2 proves in Lean that the new statement implies it.

## Encoding notes

* "Permuted" is read as an enumeration `f : ℕ → ℕ` with range the set, injective; this needs the
  set to be infinite. (A finite part would leave a cofinite part.)

## References

No `/latex/197` fetch is in the session logs, and the page cites only Erdős and Graham.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/197.lean` (Opus 5.5 review, `opus-5-5-review/197.md`).
-/

/--
A sequence f : ℕ → ℕ contains a **monotone 3-term arithmetic progression** if
there exist indices i < j < k such that f(i) < f(j) < f(k) and they form an
arithmetic progression, i.e., f(j) - f(i) = f(k) - f(j).
(Only increasing progressions; see `HasMonotone3TermAP197` for the page's notion.)
-/
def HasMonotone3TermAP (f : ℕ → ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧
    f i < f j ∧ f j < f k ∧
    f j - f i = f k - f j

/--
A set S ⊆ ℕ **can be permuted to avoid monotone 3-term APs** if there exists
an injective enumeration of S (a bijection ℕ → S) whose induced sequence
contains no monotone 3-term arithmetic progression.
-/
def CanPermuteToAvoidMonotone3AP (S : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ, range f = S ∧ Injective f ∧ ¬HasMonotone3TermAP f

/-- The page's notion: a sequence contains a monotone 3-term arithmetic progression, increasing or
decreasing, along increasing indices. -/
def HasMonotone3TermAP197 (f : ℕ → ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧
    ((f i < f j ∧ f j < f k ∧ f j - f i = f k - f j) ∨
      (f k < f j ∧ f j < f i ∧ f i - f j = f j - f k))

/-- `S` has an enumeration with no monotone 3-term progression in the page's sense. -/
def CanPermuteToAvoid197 (S : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ, range f = S ∧ Injective f ∧ ¬HasMonotone3TermAP197 f

/--
Erdős Problem #197 [ErGr79, ErGr80]:
Can ℕ be partitioned into two sets, each of which can be permuted to avoid
monotone (increasing or decreasing) 3-term arithmetic progressions?

Asserted in the "yes" direction (Status: OPEN). If three sets are allowed then this is possible.
-/
theorem erdos_problem_197 :
    ∃ (A B : Set ℕ), A ∪ B = univ ∧ Disjoint A B ∧
      CanPermuteToAvoid197 A ∧ CanPermuteToAvoid197 B :=
  sorry

/-- The input's statement, with increasing progressions only (elementary, by the block construction
in the module docstring; not proved here). -/
theorem erdos_problem_197.variants.first_pass :
    ∃ (A B : Set ℕ), A ∪ B = univ ∧ Disjoint A B ∧
      CanPermuteToAvoidMonotone3AP A ∧ CanPermuteToAvoidMonotone3AP B :=
  sorry

/-- The page's remark (SOLVED; not proved here): with three sets it is possible. -/
theorem erdos_problem_197.variants.three_sets :
    ∃ (A B C : Set ℕ), A ∪ B ∪ C = univ ∧ Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      CanPermuteToAvoid197 A ∧ CanPermuteToAvoid197 B ∧ CanPermuteToAvoid197 C :=
  sorry

/-- An enumeration avoiding monotone progressions in the page's sense avoids the input's increasing
ones (PROVED in Lean). -/
theorem erdos_problem_197.canPermuteToAvoidMonotone3AP_of_197 {S : Set ℕ}
    (h : CanPermuteToAvoid197 S) : CanPermuteToAvoidMonotone3AP S := by
  obtain ⟨f, hr, hi, hno⟩ := h
  refine ⟨f, hr, hi, fun ⟨i, j, k, hij, hjk, h1, h2, h3⟩ => hno ⟨i, j, k, hij, hjk, Or.inl ⟨h1, h2, h3⟩⟩⟩

/-- So the page's statement implies the input's (PROVED in Lean); the converse fails in spirit, since
the input's statement is elementary. -/
theorem erdos_problem_197.variants.first_pass_of_main
    (h : ∃ (A B : Set ℕ), A ∪ B = univ ∧ Disjoint A B ∧
      CanPermuteToAvoid197 A ∧ CanPermuteToAvoid197 B) :
    ∃ (A B : Set ℕ), A ∪ B = univ ∧ Disjoint A B ∧
      CanPermuteToAvoidMonotone3AP A ∧ CanPermuteToAvoidMonotone3AP B := by
  obtain ⟨A, B, hU, hD, hA, hB⟩ := h
  exact ⟨A, B, hU, hD, erdos_problem_197.canPermuteToAvoidMonotone3AP_of_197 hA,
    erdos_problem_197.canPermuteToAvoidMonotone3AP_of_197 hB⟩
