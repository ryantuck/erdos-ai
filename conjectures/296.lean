import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators

/-!
# Erdős Problem #296

Let N ≥ 1 and let k(N) be maximal such that there exist k pairwise disjoint
A₁, ..., Aₖ ⊆ {1, ..., N} with ∑_{n ∈ Aᵢ} 1/n = 1 for all i.

Erdős and Graham [ErGr80] asked: Estimate k(N). Is it true that k(N) = o(log N)?

Hunter and Sawhney observed that Theorem 3 of Bloom [Bl21], coupled with the
trivial greedy approach, implies k(N) = (1 - o(1)) log N. In particular,
k(N) is NOT o(log N); it grows like log N.
-/

/-- The reciprocal sum ∑_{n ∈ A} 1/n of a finite set of natural numbers. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / (n : ℚ)

/--
Erdős Problem #296 [ErGr80] (RESOLVED by Hunter–Sawhney via Bloom [Bl21]):

k(N) = (1 - o(1)) log N, where k(N) is the maximum number of pairwise
disjoint subsets of {1, ..., N} whose reciprocal sums each equal 1.

We formalize the non-trivial lower bound: for every ε > 0, for all
sufficiently large N, one can find at least ⌊(1 - ε) ln N⌋ pairwise disjoint
subsets of {1, ..., N}, each with reciprocal sum exactly 1.
-/
theorem erdos_problem_296 (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ (k : ℕ) (family : Fin k → Finset ℕ),
        (k : ℝ) ≥ (1 - ε) * Real.log (N : ℝ) ∧
        (∀ i, family i ⊆ Finset.Icc 1 N) ∧
        (∀ i j, i ≠ j → Disjoint (family i) (family j)) ∧
        (∀ i, reciprocalSum (family i) = 1) :=
  sorry
