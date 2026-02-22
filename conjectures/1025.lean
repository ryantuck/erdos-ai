import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset

noncomputable section

/-!
# Erdős Problem #1025

Let f be a function from all pairs of elements in {1,...,n} to {1,...,n} such
that f(x,y) ≠ x and f(x,y) ≠ y for all x,y. We call X ⊆ {1,...,n}
independent if whenever x,y ∈ X we have f(x,y) ∉ X.

Let g(n) be such that, in every function f, there is an independent set of
size at least g(n). Estimate g(n).

A question of Erdős and Hajnal [ErHa58], who proved
  n^{1/3} ≪ g(n) ≪ (n log n)^{1/2}.
Spencer [Sp72] proved g(n) ≫ n^{1/2}.
Conlon, Fox, and Sudakov [CFS16] proved g(n) ≪ n^{1/2}.
Thus g(n) = Θ(√n).
-/

/-- A pair function on `Fin n` assigns to each pair of distinct elements
    a third element different from both. -/
def IsValidPairFunction (n : ℕ) (f : Fin n → Fin n → Fin n) : Prop :=
  ∀ x y : Fin n, x ≠ y → f x y ≠ x ∧ f x y ≠ y

/-- A set `S ⊆ Fin n` is independent with respect to `f` if for all
    distinct `x, y ∈ S`, we have `f x y ∉ S`. -/
def IsIndependentPairSet (n : ℕ) (f : Fin n → Fin n → Fin n)
    (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x y ∉ S

/--
Erdős Problem #1025, lower bound (Spencer [Sp72]):

For every valid pair function f on Fin n, there exists an independent set
of size at least C · √n, for some absolute constant C > 0.
-/
theorem erdos_problem_1025_lower :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, ∀ f : Fin n → Fin n → Fin n,
    IsValidPairFunction n f →
    ∃ S : Finset (Fin n), IsIndependentPairSet n f S ∧
      (S.card : ℝ) ≥ C * Real.sqrt n :=
  sorry

/--
Erdős Problem #1025, upper bound (Conlon–Fox–Sudakov [CFS16]):

There exists a constant C > 0 such that for all sufficiently large n,
there exists a valid pair function f on Fin n for which every independent
set has size at most C · √n.
-/
theorem erdos_problem_1025_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∃ f : Fin n → Fin n → Fin n, IsValidPairFunction n f ∧
    ∀ S : Finset (Fin n), IsIndependentPairSet n f S →
      (S.card : ℝ) ≤ C * Real.sqrt n :=
  sorry

end
