import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/--
A set A ⊆ ℕ has positive upper density if there exists δ > 0 such that for
arbitrarily large N, |A ∩ {1, …, N}| / N ≥ δ.
-/
def HasPositiveUpperDensity487 (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
    (((Icc 1 N).filter (· ∈ A)).card : ℝ) ≥ δ * (N : ℝ)

/--
Erdős Problem #487 [Er61,p.236][Er65b,p.228]:

Let A ⊆ ℕ have positive upper density. Must there exist distinct a, b, c ∈ A
such that [a, b] = c (where [a, b] denotes the least common multiple of a
and b)?

This is true, a consequence of the positive solution to Erdős Problem 447
by Kleitman [Kl71].
-/
theorem erdos_problem_487 (A : Set ℕ) (hA : HasPositiveUpperDensity487 A) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Nat.lcm a b = c :=
  sorry

end
