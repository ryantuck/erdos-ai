-- [AI - Claude Opus 5.5]: Erdős Problem 172 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős Problem #172

*Source:* [erdosproblems.com/172](https://www.erdosproblems.com/172) (status **OPEN**: "This is open,
and cannot be resolved with a finite computation."; captured 2026-03-05; page edited 01 February
2026). [Er77c] [ErGr79] [ErGr80]

Is it true that in any finite colouring of $\mathbb{N}$ there exist arbitrarily large finite $A$
such that all sums and products of distinct elements in $A$ are the same colour?

Remarks recorded on the page: first asked by Hindman. Hindman [Hi80] has proved this is false
(with 7 colours) if we ask for an infinite $A$. In [Er77c] Erdős asks about the case for an infinite
$A$ with just 2 colours. Moreira [Mo17] has proved that in any finite colouring of $\mathbb{N}$
there exist $x,y$ such that $\{x,x+y,xy\}$ are all the same colour. Alweiss [Al23] has proved
that, in any finite colouring of $\mathbb{Q}\setminus\{0\}$ there exist arbitrarily large finite
$A$ such that all sums and products of distinct elements in $A$ are the same colour. Bowen and
Sabok [BoSa22] had proved this earlier for the first non-trivial case of $|A|=2$.

## Encoding notes

* "All sums and products of distinct elements in $A$" are $\sum_{s\in S}s$ and $\prod_{s\in S}s$
  for every **nonempty** $S\subseteq A$, so the elements of $A$ themselves are included. This is
  the reading of the cited results: the case $|A|=2$ of [BoSa22] is $\{x,y,x+y,xy\}$, and
  Moreira's configuration contains $x$. Upstream uses the same reading (`S.Nonempty`).
* The input required `2 ≤ S.card`, which drops the condition on the elements themselves. That
  statement is implied by the main theorem (`variants.first_pass_of_main`, PROVED) and is kept as
  `variants.first_pass`.
* The question is a yes/no question with open status; the "yes" direction is asserted.
* `ℕ` contains `0`, which does not matter: the main theorem is equivalent to its version with
  `A` of positive integers (`variants.main_iff_pos`, PROVED; remove `0` from `A`).

## References

* [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III_. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72. (Site `/latex/460` and others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)
* [Hi80] (Hindman, 1980), [Mo17] (Moreira, 2017), [Al23] (Alweiss, 2023), [BoSa22] (Bowen and
  Sabok, 2022): **DEFERRED**; no site entry was recovered.

*Provenance:* second pass of `conjectures/172.lean` (Opus 5.5 review, `opus-5-5-review/172.md`).
-/

/--
Erdős Problem #172 [Er77c, ErGr79, ErGr80] (OPEN; second pass):

In any finite colouring of ℕ there exist arbitrarily large finite sets A such
that all sums and products of distinct elements in A are the same colour:
for every nonempty subset S ⊆ A, the sum ∑ S and the product ∏ S both have
the same colour c.
-/
theorem erdos_problem_172 :
    ∀ (k : ℕ), 1 ≤ k →
    ∀ (f : ℕ → Fin k) (n : ℕ),
    ∃ (A : Finset ℕ) (c : Fin k),
      n ≤ A.card ∧
      ∀ (S : Finset ℕ), S ⊆ A → S.Nonempty →
        f (S.sum id) = c ∧ f (S.prod id) = c :=
  sorry

/--
The input's statement (first pass), kept for reference. It quantifies only over subsets with at
least two elements, so the elements of A need not have colour c. It is weaker than the main theorem
(`first_pass_of_main`).

Erdős Conjecture (Problem #172) [Er77c, ErGr79, ErGr80]:

In any finite colouring of ℕ there exist arbitrarily large finite sets A such
that all sums and products of distinct elements in A are the same colour.

Here "sums and products of distinct elements" means: for every subset S ⊆ A
with |S| ≥ 2, the sum ∑ S and the product ∏ S both have the same colour c.
-/
theorem erdos_problem_172.variants.first_pass :
    ∀ (k : ℕ), 1 ≤ k →
    ∀ (f : ℕ → Fin k) (n : ℕ),
    ∃ (A : Finset ℕ) (c : Fin k),
      n ≤ A.card ∧
      ∀ (S : Finset ℕ), S ⊆ A → 2 ≤ S.card →
        f (S.sum id) = c ∧ f (S.prod id) = c :=
  sorry

/-- The main theorem implies the input's statement (PROVED in Lean). -/
theorem erdos_problem_172.variants.first_pass_of_main
    (h : ∀ (k : ℕ), 1 ≤ k →
      ∀ (f : ℕ → Fin k) (n : ℕ),
      ∃ (A : Finset ℕ) (c : Fin k),
        n ≤ A.card ∧
        ∀ (S : Finset ℕ), S ⊆ A → S.Nonempty →
          f (S.sum id) = c ∧ f (S.prod id) = c) :
    ∀ (k : ℕ), 1 ≤ k →
    ∀ (f : ℕ → Fin k) (n : ℕ),
    ∃ (A : Finset ℕ) (c : Fin k),
      n ≤ A.card ∧
      ∀ (S : Finset ℕ), S ⊆ A → 2 ≤ S.card →
        f (S.sum id) = c ∧ f (S.prod id) = c := by
  intro k hk f n
  obtain ⟨A, c, hn, hA⟩ := h k hk f n
  exact ⟨A, c, hn, fun S hS h2 => hA S hS (Finset.card_pos.mp (by omega))⟩

/-- `0` is harmless: the main theorem is equivalent to its version with `A` a set of positive
integers (PROVED in Lean). -/
theorem erdos_problem_172.variants.main_iff_pos :
    (∀ (k : ℕ), 1 ≤ k →
      ∀ (f : ℕ → Fin k) (n : ℕ),
      ∃ (A : Finset ℕ) (c : Fin k),
        n ≤ A.card ∧
        ∀ (S : Finset ℕ), S ⊆ A → S.Nonempty →
          f (S.sum id) = c ∧ f (S.prod id) = c) ↔
    (∀ (k : ℕ), 1 ≤ k →
      ∀ (f : ℕ → Fin k) (n : ℕ),
      ∃ (A : Finset ℕ) (c : Fin k),
        n ≤ A.card ∧ (∀ a ∈ A, 0 < a) ∧
        ∀ (S : Finset ℕ), S ⊆ A → S.Nonempty →
          f (S.sum id) = c ∧ f (S.prod id) = c) := by
  constructor
  · intro h k hk f n
    obtain ⟨A, c, hn, hA⟩ := h k hk f (n + 1)
    refine ⟨A.erase 0, c, ?_, fun a ha => Nat.pos_of_ne_zero (Finset.ne_of_mem_erase ha),
      fun S hS hne => hA S (hS.trans (Finset.erase_subset 0 A)) hne⟩
    have := Finset.pred_card_le_card_erase (s := A) (a := 0)
    omega
  · intro h k hk f n
    obtain ⟨A, c, hn, -, hA⟩ := h k hk f n
    exact ⟨A, c, hn, hA⟩

/-- Hindman [Hi80] (SOLVED; not proved here): the infinite version is false with 7 colours. -/
theorem erdos_problem_172.variants.hindman :
    ∃ f : ℕ → Fin 7, ¬ ∃ (A : Set ℕ) (c : Fin 7), A.Infinite ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ (S : Finset ℕ), (S : Set ℕ) ⊆ A → S.Nonempty →
        f (S.sum id) = c ∧ f (S.prod id) = c :=
  sorry

/-- Moreira [Mo17] (SOLVED; not proved here): in any finite colouring of ℕ some `{x, x + y, x y}`
with `x, y ≥ 1` is monochromatic. -/
theorem erdos_problem_172.variants.moreira :
    ∀ (k : ℕ), 1 ≤ k → ∀ (f : ℕ → Fin k),
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ f x = f (x + y) ∧ f (x + y) = f (x * y) :=
  sorry

/-- Alweiss [Al23] (SOLVED; not proved here): the statement holds for colourings of `ℚ \ {0}`.
Stated here for colourings of `ℚ` with `0 ∉ A`: such a colouring restricts to one of `ℚ \ {0}`,
and in Alweiss's theorem the sums and products are coloured, hence nonzero, so this form follows. -/
theorem erdos_problem_172.variants.alweiss :
    ∀ (k : ℕ), 1 ≤ k →
    ∀ (f : ℚ → Fin k) (n : ℕ),
    ∃ (A : Finset ℚ) (c : Fin k),
      n ≤ A.card ∧ 0 ∉ A ∧
      ∀ (S : Finset ℚ), S ⊆ A → S.Nonempty →
        f (S.sum id) = c ∧ f (S.prod id) = c :=
  sorry
