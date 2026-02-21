import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

open Finset BigOperators

/-!
# Erdős Problem #403

Does the equation 2^m = a₁! + ⋯ + aₖ! with a₁ < a₂ < ⋯ < aₖ have only
finitely many solutions?

Asked by Burr and Erdős. Frankl and Lin independently showed that the answer
is yes, and the largest solution is 2⁷ = 2! + 3! + 5!.
-/

/--
Erdős Problem #403 [ErGr80, p.79]:

The equation 2^m = a₁! + ⋯ + aₖ! with a₁ < a₂ < ⋯ < aₖ has only finitely
many solutions. Here a solution is a pair (m, S) where m is a natural number
and S is a nonempty finite set of natural numbers whose factorials sum to 2^m.
-/
theorem erdos_problem_403 :
    Set.Finite {p : ℕ × Finset ℕ | p.2.Nonempty ∧
      ∑ a ∈ p.2, Nat.factorial a = 2 ^ p.1} :=
  sorry
