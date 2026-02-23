import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Filter Real

noncomputable section

/-- The number of subgroups of the symmetric group Sₙ. -/
noncomputable def numSubgroups (n : ℕ) : ℕ :=
  Nat.card (Subgroup (Equiv.Perm (Fin n)))

/-!
# Erdős Problem #1162

Give an asymptotic formula for the number of subgroups of Sₙ.
Is there a statistical theorem on their order?

A problem of Erdős and Turán.

Let f(n) count the number of subgroups of Sₙ.
Pyber [Py93] proved that log f(n) ≍ n².
Roney-Dougal and Tracey [RoTr25] proved that log f(n) = (1/16 + o(1))n².

Tags: group theory
-/

/--
Erdős Problem #1162 (partially resolved by Roney-Dougal and Tracey [RoTr25]):

log f(n) / n² → 1/16 as n → ∞, where f(n) is the number of subgroups of Sₙ.

The full problem, asking for an asymptotic formula for f(n) and a statistical
theorem on the orders of subgroups, remains open.
-/
theorem erdos_problem_1162 :
    Tendsto (fun n : ℕ => Real.log (numSubgroups n : ℝ) / ((n : ℝ) ^ 2))
      atTop (nhds (1 / 16)) :=
  sorry

end
