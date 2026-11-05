-- [AI - Claude Opus 5.5]: Erdős Problem 195 — second-pass formalization
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.NormNum

open Equiv

/-!
# Erdős Problem #195

*Source:* [erdosproblems.com/195](https://www.erdosproblems.com/195) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; captured 2026-03-05). [ErGr79] [ErGr80]

What is the largest $k$ such that in any permutation of $\mathbb{Z}$ there must exist a monotone
$k$-term arithmetic progression $x_1<\cdots<x_k$?

Remarks recorded on the page: Geneson [Ge19] proved that $k\leq 5$. Adenwalla [Ad22] proved that
$k\leq 4$. See also [194] and [196].

## Encoding notes

* The question asks for a value. The page records only the upper bounds $k\le5$ and $k\le4$; the
  value itself has no formal target here.
* The theorem asserts the lower bound $k\ge3$: every permutation of $\mathbb Z$ has a monotone
  3-term progression. The input's docstring calls this known ("at least 3"); the page does not
  record it, and its source was not checked in this review. It is a bound on the answer, not the
  answer.
* A permutation of $\mathbb Z$ is read as a bijection `ℤ → ℤ`, monotone on the positions
  `a, a+d, …`. Applying this to `σ⁻¹` gives the other common reading (values in progression,
  appearing in monotone order), so the two "every permutation" statements are equivalent.
  Upstream `formal-conjectures` instead reads a permutation of $\mathbb Z$ as a one-sided
  arrangement `ℕ ≃ ℤ`.
* Every permutation has monotone progressions of length `2` (`hasMonotoneAP_two`, PROVED in Lean),
  so the set of admissible `k` always contains `0, 1, 2`.

## References

No `/latex/195` fetch is in the session logs; the two papers below are from upstream
(`2befc3a`) and are **DEFERRED** as site entries.
* [Ad22] Adenwalla, S., _Avoiding monotone arithmetic progressions in permutations of integers_.
  arXiv:2211.04451 (2022).
* [Ge19] Geneson, Jesse, _Forbidden arithmetic progressions in permutations of subsets of the
  integers_. Discrete Math. (2019), 1489–1491.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171.)

*Provenance:* second pass of `conjectures/195.lean` (Opus 5.5 review, `opus-5-5-review/195.md`).
-/

/--
A permutation σ of ℤ contains a **monotone k-term arithmetic progression** if
there exist integers a and d with d > 0 such that σ is monotone (either
increasing or decreasing) on the arithmetic progression a, a+d, …, a+(k-1)d.
-/
def HasMonotoneAP (σ : Perm ℤ) (k : ℕ) : Prop :=
  ∃ a d : ℤ, 0 < d ∧
    ((∀ i j : ℕ, i < j → j < k → σ (a + ↑i * d) < σ (a + ↑j * d)) ∨
     (∀ i j : ℕ, i < j → j < k → σ (a + ↑j * d) < σ (a + ↑i * d)))

/--
Erdős Problem #195 [ErGr79, ErGr80], lower bound:

Every permutation of ℤ contains a monotone 3-term arithmetic progression, i.e. the largest `k`
asked for is at least `3`. This is a bound on the answer, not the answer; the page records only the
upper bounds `k ≤ 5` [Ge19] and `k ≤ 4` [Ad22], and the lower bound's status is the first pass's
claim (not recorded on the page; not checked here).
-/
theorem erdos_problem_195 (σ : Perm ℤ) : HasMonotoneAP σ 3 :=
  sorry

/-- Adenwalla's bound [Ad22] (SOLVED; not proved here): some permutation of ℤ has no monotone
5-term progression, so the answer is at most `4`. -/
theorem erdos_problem_195.variants.adenwalla : ∃ σ : Perm ℤ, ¬ HasMonotoneAP σ 5 :=
  sorry

/-- A monotone `l`-term progression contains a monotone `k`-term one for `k ≤ l` (PROVED in Lean). -/
theorem erdos_problem_195.hasMonotoneAP_mono {σ : Perm ℤ} {k l : ℕ} (hkl : k ≤ l)
    (h : HasMonotoneAP σ l) : HasMonotoneAP σ k := by
  obtain ⟨a, d, hd, h | h⟩ := h
  · exact ⟨a, d, hd, Or.inl fun i j hij hj => h i j hij (lt_of_lt_of_le hj hkl)⟩
  · exact ⟨a, d, hd, Or.inr fun i j hij hj => h i j hij (lt_of_lt_of_le hj hkl)⟩

/-- Geneson's bound [Ge19] (no monotone 6-term progression for some permutation, so the answer is at
most `5`) follows from Adenwalla's (PROVED in Lean). -/
theorem erdos_problem_195.variants.geneson_of_adenwalla
    (h : ∃ σ : Perm ℤ, ¬ HasMonotoneAP σ 5) : ∃ σ : Perm ℤ, ¬ HasMonotoneAP σ 6 := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, fun h6 => hσ (erdos_problem_195.hasMonotoneAP_mono (by norm_num) h6)⟩

/-- Every permutation has a monotone 2-term progression (PROVED in Lean): `σ 0 ≠ σ 1`. -/
theorem erdos_problem_195.hasMonotoneAP_two (σ : Perm ℤ) : HasMonotoneAP σ 2 := by
  have hne : σ 0 ≠ σ 1 := fun h => absurd (σ.injective h) (by decide)
  refine ⟨0, 1, one_pos, ?_⟩
  rcases lt_or_gt_of_ne hne with h | h
  · refine Or.inl fun i j hij hj => ?_
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 1 := by omega
    simpa using h
  · refine Or.inr fun i j hij hj => ?_
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 1 := by omega
    simpa using h
