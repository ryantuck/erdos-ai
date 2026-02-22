import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Classical Filter MeasureTheory Finset

noncomputable section

/-!
# Erdős Problem #992

Let x₁ < x₂ < ⋯ be an infinite sequence of integers. Is it true that, for
almost all α ∈ [0,1], the discrepancy
  D(N) = max_{I ⊆ [0,1]} |#{n ≤ N : {α xₙ} ∈ I} - |I| · N|
satisfies D(N) ≪ N^{1/2} (log N)^{o(1)}? Or even D(N) ≪ N^{1/2} (log log N)^{O(1)}?

Erdős and Koksma [ErKo49] and Cassels [Ca50] independently proved that, for any
sequence xᵢ and almost all α, D(N) ≪ N^{1/2} (log N)^{5/2 + o(1)}. Baker [Ba81]
improved this to D(N) ≪ N^{1/2} (log N)^{3/2 + o(1)}.

This was disproved by Berkes and Philipp [BePh94], who constructed a sequence
of integers x₁ < x₂ < ⋯ such that, for almost all α ∈ [0,1],
  limsup_{N → ∞} D(N) / (N log N)^{1/2} > 0.
-/

/-- The discrepancy of the sequence {α · x(n)} (mod 1) with respect to
    subintervals of [0,1).
    D(N) = sup_{0 ≤ a < b ≤ 1} |#{n < N : {α · x(n)} ∈ [a, b)} - (b - a) · N|. -/
def discrepancy992 (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
    d = abs (((Finset.range N).filter (fun n =>
      a ≤ Int.fract (α * (x n : ℝ)) ∧ Int.fract (α * (x n : ℝ)) < b)).card -
      (b - a) * (N : ℝ))}

/--
Erdős Problem #992 (disproved by Berkes and Philipp [BePh94]):

There exists a strictly increasing sequence of positive integers x₁ < x₂ < ⋯
such that for almost all α ∈ [0,1],
  limsup_{N → ∞} D(N) / (N log N)^{1/2} > 0.

Formulated as: for a.e. α, there exists c > 0 and infinitely many N with
  D(N) ≥ c · √(N · log N).
-/
theorem erdos_problem_992 :
    ∃ (x : ℕ → ℤ), StrictMono x ∧ (∀ n, 0 < x n) ∧
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∃ c : ℝ, c > 0 ∧
        ∃ᶠ N in atTop,
          discrepancy992 x α N ≥ c * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) :=
  sorry

end
