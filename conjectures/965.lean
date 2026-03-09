import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Data.Real.Basic

open Cardinal Set

/--
Erdős Problem #965 [Er75b]:

Is it true that, for any 2-colouring of ℝ, there is a set A ⊆ ℝ of
cardinality ℵ₁ such that all sums a + b with a ≠ b and a, b ∈ A are the
same colour?

This was disproved: Komjáth (2016) and independently Soukup and Weiss
proved that there exists a 2-colouring of ℝ such that for any uncountable
A ⊆ ℝ, the set {a + b | a ≠ b, a, b ∈ A} is not monochromatic.
-/
theorem erdos_problem_965 :
    ∀ (c : ℝ → Fin 2),
      ∃ (A : Set ℝ), Cardinal.mk A = aleph 1 ∧
        ∃ (color : Fin 2), ∀ a ∈ A, ∀ b ∈ A, a ≠ b → c (a + b) = color :=
  sorry
