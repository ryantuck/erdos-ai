import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #1026

Let x₁, …, xₙ be a sequence of distinct real numbers. Determine
  max(∑ x_{iᵣ}),
where the maximum is taken over all monotonic subsequences.

The precise formulation (van Doorn): What is the largest constant c such that,
for all sequences of n real numbers x₁, …, xₙ,
  max(∑ x_{iᵣ}) > (c - o(1)) · (1/√n) · ∑ xᵢ
where the maximum is over all monotonic subsequences?

Cambie conjectured the stronger statement: if x₁, …, x_{k²} are distinct
positive real numbers with ∑ xᵢ = 1, then there is always a monotonic
subsequence with sum at least 1/k. This shows c = 1.

This was proved by Tidor, Wang, and Yang [TWY16], and is also implicit in
work of Wagner [Wa17]. It has been formalised in Lean.
-/

/-- A set of indices forms an increasing subsequence of `x` if for all
    pairs of indices in the set, the one with larger index has larger value. -/
def IsIncreasingSubseq {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i < j → x i < x j

/-- A set of indices forms a decreasing subsequence of `x` if for all
    pairs of indices in the set, the one with larger index has smaller value. -/
def IsDecreasingSubseq {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i < j → x i > x j

/-- A set of indices forms a monotone subsequence if it is either
    increasing or decreasing. -/
def IsMonotoneSubseq {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  IsIncreasingSubseq x S ∨ IsDecreasingSubseq x S

/--
Erdős Problem #1026 (Cambie's conjecture, proved by Tidor–Wang–Yang [TWY16]):

If x₁, …, x_{k²} are distinct positive real numbers summing to 1, then
there exists a monotone subsequence whose sum is at least 1/k.

This is a weighted form of the Erdős–Szekeres theorem.
-/
theorem erdos_problem_1026 (k : ℕ) (hk : k ≥ 1)
    (x : Fin (k ^ 2) → ℝ)
    (hx_pos : ∀ i, x i > 0)
    (hx_inj : Function.Injective x)
    (hx_sum : ∑ i, x i = 1) :
    ∃ S : Finset (Fin (k ^ 2)), IsMonotoneSubseq x S ∧
      ∑ i ∈ S, x i ≥ 1 / (k : ℝ) :=
  sorry

end
