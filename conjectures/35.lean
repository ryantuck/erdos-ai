import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Classical Finset BigOperators

noncomputable section

/-- The sumset A + B: the set of all a + b with a ∈ A, b ∈ B. -/
def sumset35 (A B : Set ℕ) : Set ℕ := {n : ℕ | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/-- Schnirelmann density of a set A ⊆ ℕ:
    d_s(A) = inf_{N ≥ 1} |A ∩ {1, …, N}| / N -/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  sInf {x : ℝ | ∃ N : ℕ, N ≥ 1 ∧ x = ((Icc 1 N).filter (· ∈ A)).card / (N : ℝ)}

/-- A set B ⊆ ℕ is an additive basis of order k if every natural number
    can be written as a sum of exactly k elements from B (with repetition).
    Since 0 ∈ B is assumed separately, "exactly k" is equivalent to "at most k". -/
def IsAdditiveBasis35 (B : Set ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, ∃ f : Fin k → ℕ, (∀ i, f i ∈ B) ∧ ∑ i, f i = n

/--
**Erdős Problem #35** (Proved):

Let B ⊆ ℕ be an additive basis of order k with 0 ∈ B. Is it true that for every
A ⊆ ℕ we have d_s(A + B) ≥ α + α(1 - α)/k, where α = d_s(A) is the
Schnirelmann density?

This was proved by Plünnecke [Pl70], who showed the stronger inequality
d_s(A + B) ≥ α^{1-1/k}, as observed by Ruzsa.
-/
theorem erdos_problem_35
    (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis35 B k) (h0 : (0 : ℕ) ∈ B) :
    let α := schnirelmannDensity A
    schnirelmannDensity (sumset35 A B) ≥ α + α * (1 - α) / (k : ℝ) :=
  sorry

end
