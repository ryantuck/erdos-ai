import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Finite.Basic

open Finset BigOperators

/-- The set of all finite subset sums of a set A ⊆ ℕ. That is,
    P(A) = {∑_{n ∈ B} n : B ⊆ A, B finite}. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {s | ∃ (B : Finset ℕ), (↑B : Set ℕ) ⊆ A ∧ s = ∑ n ∈ B, n}

/-- The threshold of completeness T(A): the least m such that
    all n ≥ m are in P(A), the set of finite subset sums of A.
    (Only meaningful for complete sequences.) -/
noncomputable def thresholdOfCompleteness (A : Set ℕ) : ℕ :=
  sInf {m : ℕ | ∀ n : ℕ, n ≥ m → n ∈ subsetSums A}

/-- The set of k-th powers of positive integers: {1^k, 2^k, 3^k, ...}. -/
def kthPowers (k : ℕ) : Set ℕ :=
  {m | ∃ n : ℕ, n ≥ 1 ∧ m = n ^ k}

/--
Erdős Problem #345 [ErGr80, p.55]:

Let A ⊆ ℕ be a complete sequence, and define the threshold of completeness
T(A) to be the least integer m such that all n ≥ m are in
P(A) = {∑_{n ∈ B} n : B ⊆ A, B finite}.

Is it true that there are infinitely many k such that T(n^k) > T(n^{k+1})?

Known values: T(n) = 1, T(n²) = 128, T(n³) = 12758, T(n⁴) = 5134240,
and T(n⁵) = 67898771.
-/
theorem erdos_problem_345 :
    Set.Infinite {k : ℕ | thresholdOfCompleteness (kthPowers k) >
      thresholdOfCompleteness (kthPowers (k + 1))} :=
  sorry
