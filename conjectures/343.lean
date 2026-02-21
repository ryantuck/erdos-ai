import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Classical BigOperators

/-- The counting function for a multiset represented by multiplicities:
    number of elements (with multiplicity) in {1, ..., N}. -/
def countUpTo343 (mult : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, mult (k + 1)

/-- The set of all finite subset sums P(A) of a multiset.
    A finite submultiset is b : ℕ →₀ ℕ with b n ≤ mult n for all n.
    The sum is Σ n * b(n). -/
def subsetSums343 (mult : ℕ → ℕ) : Set ℕ :=
  {s : ℕ | ∃ (b : ℕ →₀ ℕ), (∀ n, b n ≤ mult n) ∧ s = b.sum (fun n k => n * k)}

/-- A set of natural numbers contains an infinite arithmetic progression
    {a + n * d : n ∈ ℕ} for some a ≥ 0 and d > 0. -/
def containsInfiniteAP343 (S : Set ℕ) : Prop :=
  ∃ (a d : ℕ), 0 < d ∧ ∀ n : ℕ, a + n * d ∈ S

/--
Erdős Problem #343 [ErGr80, p.54]:

If A ⊆ ℕ is a multiset of integers such that |A ∩ {1, ..., N}| ≫ N for all N,
must A be subcomplete? That is, must P(A) = {Σ_{n∈B} n : B ⊆ A finite}
contain an infinite arithmetic progression?

A problem of Folkman. Proved by Szemerédi and Vu [SzVu06].
-/
theorem erdos_problem_343 :
    ∀ (mult : ℕ → ℕ),
      mult 0 = 0 →
      (∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N → c * (N : ℝ) ≤ (countUpTo343 mult N : ℝ)) →
      containsInfiniteAP343 (subsetSums343 mult) :=
  sorry
