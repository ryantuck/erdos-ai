-- [AI - Claude Opus 5.5]: Erdős Problem 196 — second-pass formalization
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Nat.Find

open Equiv

/-!
# Erdős Problem #196

*Source:* [erdosproblems.com/196](https://www.erdosproblems.com/196) (status **OPEN** at capture:
"This is open, and cannot be resolved with a finite computation."; captured 2026-03-05).
[ErGr79] [ErGr80]

Must every permutation of $\mathbb{N}$ contain a monotone 4-term arithmetic progression? In other
words, given a permutation $x$ of $\mathbb{N}$ must there be indices with either $i<j<k<l$ or
$i>j>k>l$ such that $x_i,x_j,x_k,x_l$ are an arithmetic progression?

Remarks recorded on the page: Davis, Entringer, Graham, and Simmons [DEGS77] have shown that there
must exist a monotone 3-term arithmetic progression and need not contain a 5-term arithmetic
progression. See also [194] and [195].

## Status after capture, and the fix

Upstream `formal-conjectures` (`2befc3a`) records the answer **no**: Ho [Ho26] constructs an
explicit permutation of the positive integers with no monotone 4-term arithmetic progression, and
Lean proofs of the negation are linked (Kruer and Kohlmeyer; `coleski/erdos196`). The metadata
mirror (`c443d8c`) still lists the problem as open. Neither the paper nor the proofs were read in
this review.

The input asserted the "yes" answer. v2 states the recorded answer (the negation) with `sorry`.

## Encoding notes

* The input's form (indices `i < j < k < l`, any nonzero common difference) is the page's: a
  progression read along decreasing indices is a progression read the other way. The common
  difference cannot be `0`, since `σ` is injective.
* The [DEGS77] 3-term result has a short proof, formalized here (`variants.degs_three`, PROVED in
  Lean): with `a = σ 0`, let `j` be the first position with `σ j > a`; the value `2σ(j) − a` exceeds
  every value at positions `1, …, j−1` and `σ j` itself, so it appears after `j`.

## References

No `/latex/196` fetch is in the session logs; the entries below are from upstream (`2befc3a`) and
are **DEFERRED** as site entries.
* [DEGS77] Davis, J. A., Entringer, R. C., Graham, R. L. and Simmons, G. J., _On permutations
  containing no long arithmetic progressions_. Acta Arith. (1977), 81–90.
* [Ho26] Ho, Boon Suan, _A 4AP-free permutation of the positive integers_. arXiv:2609.12780 (2026).
  (Not read.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171.)

*Provenance:* second pass of `conjectures/196.lean` (Opus 5.5 review, `opus-5-5-review/196.md`).
-/

/--
Erdős Problem #196 [ErGr79, ErGr80], with the answer recorded after the capture: **no**.

Some permutation of ℕ contains no monotone 4-term arithmetic progression: there are no indices
i < j < k < l with x(i), x(j), x(k), x(l) an arithmetic progression.

(Status: OPEN at capture; recorded as solved in the negative by upstream [Ho26], unverified here;
the mirror still lists it as open.)
-/
theorem erdos_problem_196 :
    ¬ ∀ σ : Perm ℕ,
      ∃ i j k l : ℕ, i < j ∧ j < k ∧ k < l ∧
        (σ j : ℤ) - (σ i : ℤ) = (σ k : ℤ) - (σ j : ℤ) ∧
        (σ k : ℤ) - (σ j : ℤ) = (σ l : ℤ) - (σ k : ℤ) :=
  sorry

/-- [DEGS77] (PROVED in Lean): every permutation of ℕ contains a monotone 3-term arithmetic
progression `σ i, σ j, σ k` with `i < j < k`. -/
theorem erdos_problem_196.variants.degs_three (σ : Perm ℕ) :
    ∃ i j k : ℕ, i < j ∧ j < k ∧ (σ j : ℤ) - (σ i : ℤ) = (σ k : ℤ) - (σ j : ℤ) := by
  classical
  have hex : ∃ j, σ 0 < σ j := ⟨σ.symm (σ 0 + 1), by simp⟩
  have hj : σ 0 < σ (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, ¬ σ 0 < σ m := fun m hm => Nat.find_min hex hm
  have hσk : σ (σ.symm (2 * σ (Nat.find hex) - σ 0)) = 2 * σ (Nat.find hex) - σ 0 := by simp
  have hj0 : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hj
      exact absurd hj (lt_irrefl _)
    · exact h
  have hjk : Nat.find hex < σ.symm (2 * σ (Nat.find hex) - σ 0) := by
    rcases lt_trichotomy (σ.symm (2 * σ (Nat.find hex) - σ 0)) (Nat.find hex) with h | h | h
    · exfalso
      have := hmin _ h
      rw [hσk] at this
      omega
    · exfalso
      rw [h] at hσk
      omega
    · exact h
  refine ⟨0, Nat.find hex, σ.symm (2 * σ (Nat.find hex) - σ 0), hj0, hjk, ?_⟩
  rw [hσk]
  omega

/-- [DEGS77] (SOLVED; not proved here): some permutation of ℕ has no monotone 5-term arithmetic
progression. -/
theorem erdos_problem_196.variants.degs_no_five :
    ∃ σ : Perm ℕ, ¬ ∃ i j k l m : ℕ, i < j ∧ j < k ∧ k < l ∧ l < m ∧
      (σ j : ℤ) - (σ i : ℤ) = (σ k : ℤ) - (σ j : ℤ) ∧
      (σ k : ℤ) - (σ j : ℤ) = (σ l : ℤ) - (σ k : ℤ) ∧
      (σ l : ℤ) - (σ k : ℤ) = (σ m : ℤ) - (σ l : ℤ) :=
  sorry
