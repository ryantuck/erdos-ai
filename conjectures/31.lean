import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical Filter

/-- The sumset `A + B`: the set of all `a + b` with `a ∈ A, b ∈ B`. -/
def sumset31 (A B : Set ℕ) : Set ℕ := {n : ℕ | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/-- A set `B ⊆ ℕ` has natural density zero if
    `|B ∩ {0, …, N-1}| / N → 0` as `N → ∞`. -/
def HasNaturalDensityZero (B : Set ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (((Finset.range N).filter (· ∈ B)).card : ℝ) / (N : ℝ) < ε

/--
**Erdős Problem #31** (Erdős–Straus, proved by Lorentz [Lo54]):

Given any infinite set $A \subset \mathbb{N}$, there exists a set $B \subseteq \mathbb{N}$
of natural density $0$ such that $A + B$ contains all except finitely many natural numbers.
-/
theorem erdos_problem_31 (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, HasNaturalDensityZero B ∧
      Set.Finite {n : ℕ | n ∉ sumset31 A B} :=
  sorry
