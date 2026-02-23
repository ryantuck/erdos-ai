import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic

noncomputable section

attribute [local instance] Classical.propDecidable

open Equiv

/-- A natural number m is a subgroup order of Sₙ if there exists a subgroup
    of the symmetric group Perm(Fin n) with exactly m elements. -/
def IsSubgroupOrderOfSn (n m : ℕ) : Prop :=
  ∃ H : Subgroup (Perm (Fin n)), Nat.card H = m

/--
Erdős Problem #1163 (Erdős and Turán):
Describe (by statistical means) the arithmetic structure of the orders of
subgroups of Sₙ.

The original problem [Va99, 5.74] is acknowledged as ambiguous. A concrete
interpretation: as n → ∞, the proportion of divisors of n! that are orders
of subgroups of Sₙ tends to 0. By Lagrange's theorem, every subgroup order
divides n!, but the set of subgroup orders becomes a vanishingly small
fraction of all divisors.
-/
theorem erdos_problem_1163 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n ≥ N,
        ((n.factorial.divisors.filter (fun m => IsSubgroupOrderOfSn n m)).card : ℝ) <
        ε * (n.factorial.divisors.card : ℝ) := by
  sorry

end
