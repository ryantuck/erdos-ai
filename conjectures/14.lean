import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Nat
open scoped Classical

/--
The set of sums of two elements from A that are representable in exactly one way.
Order does not matter in the sum (so {x, y} is the same as {y, x}), and x can equal y.
This matches the definition of r_A(n) = |{(a, b) ∈ A × A : a ≤ b, a + b = n}|.
-/
noncomputable def Erdos14UniqueSums (A : Set ℕ) : Set ℕ :=
  { n : ℕ | ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n)).card = 1 }

/--
Erdős Problem #14:
Let A ⊆ ℕ. Let B ⊆ ℕ be the set of integers representable in exactly one way as the sum
of two elements from A.
Is it true that for all ε > 0 and large N, |{1, ..., N} \ B| ≫_ε N^(1/2 - ε)?
-/
theorem erdos_problem_14_conjecture :
  ∀ A : Set ℕ,
  ∀ ε : ℝ, ε > 0 →
  ∃ C : ℝ, C > 0 ∧
  ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
  (((Finset.range (N + 1)).filter (fun n => n > 0 ∧ n ∉ Erdos14UniqueSums A)).card : ℝ) ≥ C * (N : ℝ) ^ ((1 : ℝ) / 2 - ε) :=
sorry
