import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Basic

open MeasureTheory Set Filter Finset

noncomputable section

/-!
# Erdős Problem #996

Let n₁ < n₂ < ⋯ be a lacunary sequence of integers, and let f ∈ L²([0,1]).
Let fₙ be the nth partial sum of the Fourier series of f(x). Is there an
absolute constant C > 0 such that, if
  ‖f - fₙ‖₂ ≪ 1/(log log log n)^C
then
  lim_{N→∞} (1/N) ∑_{k≤N} f({α·nₖ}) = ∫₀¹ f(x) dx
for almost every α?

Kac, Salem, and Zygmund proved the conclusion holds if ‖f - fₙ‖₂ ≪ 1/(log n)^c
for c > 1. Erdős improved this to 1/(log log n)^c for c > 1. Matsuyama
improved this to c > 1/2.
-/

/-- A sequence is lacunary if the ratio of consecutive terms is bounded away
    from 1: there exists q > 1 such that n_{k+1} ≥ q · n_k for all k. -/
def IsLacunary (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ ∃ q : ℝ, 1 < q ∧ ∀ k : ℕ, (n (k + 1) : ℝ) ≥ q * (n k : ℝ)

/-- The L² norm of g on [0,1], i.e., (∫₀¹ |g(x)|² dx)^(1/2). -/
noncomputable def l2NormOnUnitInterval (g : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ x, g x ^ 2 ∂(volume.restrict (Icc (0 : ℝ) 1)))

/-- The nth partial sum of the Fourier series of f. We define this opaquely
    since the full Fourier series construction is not needed for stating
    the conjecture — only its approximation property matters. -/
noncomputable def fourierPartialSum : (ℝ → ℝ) → ℕ → (ℝ → ℝ) := sorry

/--
Erdős Problem #996 [Er64b]:

There exists an absolute constant C > 0 such that for any lacunary sequence
n₁ < n₂ < ⋯ of positive integers and any f ∈ L²([0,1]), if the Fourier
partial sums satisfy ‖f - fₘ‖₂ ≤ K/(log log log m)^C for some K and all
sufficiently large m, then
  lim_{N→∞} (1/N) ∑_{k≤N} f({α·nₖ}) = ∫₀¹ f(x) dx
for almost every α ∈ (0,1).
-/
theorem erdos_problem_996 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ → ℕ), IsLacunary n →
      ∀ (f : ℝ → ℝ), Measurable f →
      ∀ (K : ℝ), 0 < K →
      (∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m →
        l2NormOnUnitInterval (fun x => f x - fourierPartialSum f m x) ≤
          K / (Real.log (Real.log (Real.log (m : ℝ)))) ^ C) →
      ∀ᵐ α ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        Tendsto (fun N : ℕ =>
          (1 / (N : ℝ)) * ∑ k ∈ Finset.range N,
            f (Int.fract (α * (n k : ℝ))))
          atTop (nhds (∫ x, f x ∂(volume.restrict (Icc (0 : ℝ) 1)))) :=
  sorry

end
