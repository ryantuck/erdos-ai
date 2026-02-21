import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Classical Finset

/-- The subset sum set P(A): the set of all sums ∑_{n ∈ B} n for finite B ⊆ A. -/
def subsetSums344 (A : Set ℕ) : Set ℕ :=
  {s : ℕ | ∃ (B : Finset ℕ), (↑B : Set ℕ) ⊆ A ∧ B.sum id = s}

/-- A set of natural numbers contains an infinite arithmetic progression:
    there exist a ≥ 0 and d > 0 such that a + n·d ∈ S for all n ∈ ℕ. -/
def ContainsInfiniteAP344 (S : Set ℕ) : Prop :=
  ∃ (a d : ℕ), 0 < d ∧ ∀ n : ℕ, a + n * d ∈ S

/--
Erdős Problem #344 [ErGr80, p.54]:

If A ⊆ ℕ is a set of positive integers such that |A ∩ {1,...,N}| ≫ N^{1/2}
(i.e., there exists c > 0 and N₀ such that |A ∩ {1,...,N}| ≥ c·√N for all
N ≥ N₀), then A is subcomplete: the set P(A) of all finite subset sums of A
contains an infinite arithmetic progression.

This was proved by Szemerédi and Vu [SzVu06]. Folkman had previously proved
this under the stronger assumption |A ∩ {1,...,N}| ≥ c·N^{1/2+ε} for some
ε > 0.
-/
theorem erdos_problem_344
    (A : Set ℕ)
    (hA_pos : ∀ a ∈ A, 0 < a)
    (c : ℝ) (hc : 0 < c)
    (hgrowth : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * Real.sqrt (N : ℝ) ≤ (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) :
    ContainsInfiniteAP344 (subsetSums344 A) :=
  sorry
