import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open MeasureTheory Filter Finset Set

noncomputable section

/-!
# Erdős Problem #995

Let n₁ < n₂ < ⋯ be a lacunary sequence of integers and f ∈ L²([0,1]). Estimate
the growth of, for almost all α,
  ∑_{1 ≤ k ≤ N} f({α nₖ}).
For example, is it true that, for almost all α,
  ∑_{1 ≤ k ≤ N} f({α nₖ}) = o(N √(log log N))?

Erdős [Er49d] constructed a lacunary sequence and f ∈ L²([0,1]) such that, for
every ε > 0, for almost all α,
  limsup_{N → ∞} (1 / (N(log log N)^{1/2 - ε})) ∑_{k≤N} f({α nₖ}) = ∞.

Erdős [Er64b] thought that his lower bound was closer to the truth.
-/

/-- A sequence of positive integers is lacunary if it is strictly increasing
    and there exists q > 1 such that n(k+1) ≥ q · n(k) for all k. -/
def IsLacunary995 (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ ∃ q : ℝ, q > 1 ∧ ∀ k : ℕ, (n k : ℝ) * q ≤ n (k + 1)

/--
Erdős Problem #995 [Er64b]:

For every lacunary sequence (nₖ) of positive integers and every f ∈ L²([0,1]),
for almost all α ∈ [0,1],
  ∑_{k < N} f({α · nₖ}) = o(N · √(log log N)).

Formulated as: for every ε > 0, for almost all α, eventually (for large N),
  |∑_{k < N} f({α · nₖ})| ≤ ε · N · √(log log N).
-/
theorem erdos_problem_995
    (n : ℕ → ℕ) (hn : IsLacunary995 n)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hf_sq : Integrable (fun x => f x ^ 2) (volume.restrict (Icc (0 : ℝ) 1))) :
    ∀ ε : ℝ, ε > 0 →
    ∀ᵐ α ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        |∑ k ∈ Finset.range N, f (Int.fract (α * (n k : ℝ)))| ≤
          ε * (N : ℝ) * Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  sorry

end
