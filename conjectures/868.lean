import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Real Classical

noncomputable section

/-- The representation function 1_A ∗ 1_A(n): the number of ordered pairs (a, b) with
a, b ∈ A and a + b = n. -/
def reprFunc (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card

/-- A ⊆ ℕ is an asymptotic additive basis of order 2: every sufficiently large
natural number is a sum of two elements of A. -/
def IsAsympAddBasis2 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ a ∈ A, ∃ b ∈ A, a + b = n

/-- A ⊆ ℕ is a minimal asymptotic additive basis of order 2: it is a basis and
removing any element destroys the basis property. -/
def IsMinAsympAddBasis2 (A : Set ℕ) : Prop :=
  IsAsympAddBasis2 A ∧ ∀ x ∈ A, ¬IsAsympAddBasis2 (A \ {x})

/--
Erdős Problem #868 [ErNa79, Er92c] (DISPROVED):

If A is an additive basis of order 2 and 1_A ∗ 1_A(n) → ∞ as n → ∞,
must A contain a minimal additive basis of order 2?

A question of Erdős and Nathanson. They proved it holds when
1_A ∗ 1_A(n) > (log(4/3))⁻¹ · log n for all large n.

Disproved by Larsen and Larsen, who showed there exists a constant c > 0
and a basis A with 1_A ∗ 1_A(n) > c · log n for all large n, yet A
contains no minimal basis of order 2.
-/
theorem erdos_problem_868
    (A : Set ℕ)
    (hBasis : IsAsympAddBasis2 A)
    (hRepr : ∀ C : ℕ, ∃ N₀ : ℕ, ∀ n ≥ N₀, reprFunc A n ≥ C) :
    ∃ B : Set ℕ, B ⊆ A ∧ IsMinAsympAddBasis2 B :=
  sorry

end
