import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Nat.Lattice

open Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #785

Let A, B ⊆ ℕ be infinite sets such that A + B contains all large integers.
Let A(x) = |A ∩ [1, x]| and similarly for B(x). Is it true that if
A(x)B(x) ∼ x then A(x)B(x) - x → ∞ as x → ∞?

Such sets A and B (with all large integers in A + B and A(x)B(x) ∼ x) are
called exact additive complements. Danzer proved that exact additive
complements exist.

The answer is yes, proved by Sárközy and Szemerédi [SaSz94].
Ruzsa [Ru17] has constructed, for any function w(x) → ∞, such a pair
of sets with A(x)B(x) - x < w(x) for infinitely many x.

https://www.erdosproblems.com/785

Tags: additive combinatorics
-/

/-- Counting function: |A ∩ {1, …, x}| -/
noncomputable def countingFn785 (A : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (· ∈ A)).card

/--
**Erdős Problem #785** (PROVED — Sárközy and Szemerédi [SaSz94]):

Let A, B ⊆ ℕ be infinite sets such that A + B contains all sufficiently
large integers (i.e., A and B are additive complements). If A(x)B(x) ∼ x
(exact additive complements), then A(x)B(x) - x → ∞ as x → ∞.
-/
theorem erdos_problem_785
    (A B : Set ℕ)
    (hA_inf : Set.Infinite A)
    (hB_inf : Set.Infinite B)
    (h_complement : ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → ∃ a ∈ A, ∃ b ∈ B, a + b = n)
    (h_asymp : Tendsto
      (fun x : ℕ => (countingFn785 A x * countingFn785 B x : ℝ) / (x : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun x : ℕ => (countingFn785 A x * countingFn785 B x : ℝ) - (x : ℝ))
      atTop atTop :=
  sorry

end
