import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup

open scoped Classical
open Filter

/--
The counting function for A up to N: |A ∩ {1, …, N}|.
-/
noncomputable def countingFn40 (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/--
The representation function for a set A ⊆ ℕ, counting the number of ways
to write n as a + b with a, b ∈ A (i.e. 1_A ∗ 1_A(n)).
-/
noncomputable def repFunction40 (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A)).card

/--
Erdős Problem #40 [Er95, Er97c]:

For what functions g(N) → ∞ is it true that
  |A ∩ {1, …, N}| ≫ N^{1/2} / g(N)
implies limsup 1_A ∗ 1_A(n) = ∞?

This is a stronger form of the Erdős-Turán conjecture (#28), since
establishing this for any function g(N) → ∞ would imply a positive
solution to #28.

We state the strongest form: for ALL g → ∞, the implication holds.
-/
theorem erdos_problem_40 (g : ℕ → ℝ) (hg : Tendsto g atTop atTop)
    (A : Set ℕ)
    (hA : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N in atTop,
        (countingFn40 A N : ℝ) ≥ C * (N : ℝ) ^ ((1 : ℝ) / 2) / g N) :
    ∀ M : ℕ, ∃ n : ℕ, repFunction40 A n ≥ M :=
  sorry
