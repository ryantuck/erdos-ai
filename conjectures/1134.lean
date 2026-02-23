import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Finset Filter

noncomputable section

/-!
# Erdős Problem #1134

Let A ⊆ ℕ be the smallest set which contains 1 and is closed under the
operations x ↦ 2x+1, x ↦ 3x+1, and x ↦ 6x+1. Does A have positive
lower density?

This was disproved by Crampin and Hilton, who showed that
|A ∩ [1,X]| ≪ X^{τ+o(1)} where τ ≈ 0.900626 < 1 is the unique positive
root of 6^{-τ} + ∑_{k≥0} (3·2^k)^{-τ} = 1. In particular, A has
density 0.
-/

/-- The set A from Erdős Problem #1134: the smallest subset of ℕ containing 1
    and closed under x ↦ 2x+1, x ↦ 3x+1, and x ↦ 6x+1. -/
inductive Erdos1134.InSet : ℕ → Prop where
  | base : Erdos1134.InSet 1
  | step2 (n : ℕ) : Erdos1134.InSet n → Erdos1134.InSet (2 * n + 1)
  | step3 (n : ℕ) : Erdos1134.InSet n → Erdos1134.InSet (3 * n + 1)
  | step6 (n : ℕ) : Erdos1134.InSet n → Erdos1134.InSet (6 * n + 1)

noncomputable instance : DecidablePred Erdos1134.InSet := Classical.decPred _

/-- The counting function: |A ∩ [1, N]| for the set A from Problem #1134. -/
noncomputable def Erdos1134.count (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => Erdos1134.InSet n)).card

/--
Erdős Problem #1134 [La16]:

Let A ⊆ ℕ be the smallest set containing 1 and closed under x ↦ 2x+1,
x ↦ 3x+1, and x ↦ 6x+1. Then A does not have positive lower density;
in fact the natural density of A is 0.

Disproved (answered in the negative) by Crampin and Hilton, who showed
|A ∩ [1,X]| ≪ X^{τ+o(1)} where τ ≈ 0.900626 < 1.
-/
theorem erdos_problem_1134 :
    Tendsto (fun N : ℕ => (Erdos1134.count N : ℝ) / (N : ℝ))
      atTop (nhds 0) :=
  sorry

end
