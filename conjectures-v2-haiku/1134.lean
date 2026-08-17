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

This problem was posed by Erdős (1972, £10 prize). Crampin and Hilton
disproved the question, showing that |A ∩ [1,X]| ≪ X^{τ+o(1)} where
τ ≈ 0.900626 < 1 is the unique positive root of the Crampin–Hilton
equation. In particular, A has natural density 0 (and thus does not
have positive lower density).

The set A is defined via three affine maps with multiplicative coefficients
(2, 3, 6) whose reciprocals sum to 1: 1/2 + 1/3 + 1/6 = 1. By the
Erdős–Crampin–Hilton theory on sets closed under x ↦ mᵢx+bᵢ when
∑(1/mᵢ^σ) = 1 (with σ < 1), this condition forces density 0.

**References:**
- [La##] Lagarias, Report on Crampin–Hilton disproof [YEAR/JOURNAL DEFERRED]
- [KlRa74] Klarner & Rado [DETAILS DEFERRED]
- [Kl82] Klarner [DETAILS DEFERRED]
- [Gu83b] Guy [DETAILS DEFERRED]
- [Gu04] Guy [DETAILS DEFERRED]
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
Erdős Problem #1134:

Does the set A ⊆ ℕ (the smallest set containing 1 and closed under
x ↦ 2x+1, x ↦ 3x+1, x ↦ 6x+1) have positive lower density?

The answer is **NO**: Crampin and Hilton disproved this, showing
|A ∩ [1,X]| ≪ X^{τ+o(1)} where τ ≈ 0.900626 < 1. This implies
the natural density of A is 0, so A does not have positive lower density.
-/
theorem erdos_problem_1134 :
    answer(False) ↔ (∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop, (c : ℝ) ≤ (Erdos1134.count N : ℝ) / (N : ℝ)) := by
  sorry

namespace Erdos1134.variants

/-- Klarner's related problem: Let K ⊆ ℕ be the smallest set containing 0
    and closed under x ↦ 2x, x ↦ 3x+2, and x ↦ 6x+3. Does K have positive density?

    This variant remains open. The set K has a similar structure to the main
    problem but uses different operations with a different base element.
    (See [Kl82].) -/
inductive KlarnerSet : ℕ → Prop where
  | base : KlarnerSet 0
  | step2 (n : ℕ) : KlarnerSet n → KlarnerSet (2 * n)
  | step3 (n : ℕ) : KlarnerSet n → KlarnerSet (3 * n + 2)
  | step6 (n : ℕ) : KlarnerSet n → KlarnerSet (6 * n + 3)

noncomputable def klarner_count (N : ℕ) : ℕ :=
  ((Finset.Icc 0 N).filter (fun n => KlarnerSet n)).card

/-- Does the Klarner set have positive density? -/
theorem klarner :
    answer(sorry) ↔ (∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop, (c : ℝ) ≤ (klarner_count N : ℝ) / (N : ℝ)) := by
  sorry

end Erdos1134.variants

end
