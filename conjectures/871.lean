import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Set Filter Topology Classical

noncomputable section

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset871 (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ A, ∃ b ∈ A, n = a + b}

/-- `A ⊆ ℕ` is an additive basis of order `2` if every sufficiently large
    natural number can be written as the sum of two elements of `A`. -/
def IsAdditiveBasis2_871 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ sumset871 A

/-- The representation function r_A(n) = |{a ∈ {0,...,n} : a ∈ A ∧ n-a ∈ A}|,
    i.e., the number of ways to write n as a sum of two elements of A. -/
noncomputable def repCount871 (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A)).card

/--
Erdős Problem #871 [ErNa88] (DISPROVED):

Let A ⊆ ℕ be an additive basis of order 2, and suppose 1_A ∗ 1_A(n) → ∞
as n → ∞ (i.e., the number of representations of n as a sum of two elements
of A tends to infinity). Can A be partitioned into two disjoint additive
bases of order 2?

Erdős and Nathanson proved this is true if 1_A ∗ 1_A(n) > c log n for some
c > (log(4/3))⁻¹. They also proved [ErNa89] that for every t there exists
a basis A of order 2 with 1_A ∗ 1_A(n) ≥ t for all large n that cannot be
partitioned into two disjoint additive bases.

Disproved by Larsen using Claude Opus 4.5 — only a small modification of
the argument of [ErNa89] is required.

Formalized as the negation: there exists an additive basis A of order 2
whose representation function tends to infinity, yet A cannot be partitioned
into two disjoint additive bases of order 2.
-/
theorem erdos_problem_871 :
    ∃ A : Set ℕ,
      IsAdditiveBasis2_871 A ∧
      Tendsto (fun n => (repCount871 A n : ℝ)) atTop atTop ∧
      ¬ ∃ A₁ A₂ : Set ℕ,
        A₁ ∪ A₂ = A ∧ Disjoint A₁ A₂ ∧
        IsAdditiveBasis2_871 A₁ ∧ IsAdditiveBasis2_871 A₂ :=
  sorry

end
