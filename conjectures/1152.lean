import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Filter Polynomial MeasureTheory Set

noncomputable section

namespace Erdos1152

/-!
# Erdős Problem #1152

For n ≥ 1 fix some sequence of n distinct numbers x₁ₙ, ..., xₙₙ ∈ [-1,1].
Let ε = ε(n) → 0.

Does there always exist a continuous function f : [-1,1] → ℝ such that if pₙ is
a sequence of polynomials, with degrees deg pₙ < (1 + ε(n))n, such that
pₙ(xₖₙ) = f(xₖₙ) for all 1 ≤ k ≤ n, then pₙ(x) ↛ f(x) for almost all
x ∈ [-1,1]?

Erdős, Kroó, and Szabados [EKS89] proved that if ε > 0 is fixed (does not → 0),
then there exist sequences xᵢⱼ such that for any continuous function f, there
exists a sequence of polynomials pₙ with deg pₙ < (1+ε)n interpolating f at xₖₙ,
and pₙ(x) → f(x) uniformly for all x ∈ [-1,1].

Tags: analysis, polynomials
-/

/--
Erdős Problem #1152 [Va99, 2.42]:

For any triangular array of distinct interpolation nodes in [-1,1] and any
function ε(n) → 0, there exists a continuous function f : [-1,1] → ℝ such that
every sequence of polynomials pₙ with deg pₙ < (1 + ε(n))n interpolating f at
the nodes fails to converge to f for almost every x ∈ [-1,1].
-/
theorem erdos_problem_1152
    (x : (n : ℕ) → Fin n → ℝ)
    (hx_range : ∀ n, ∀ k : Fin n, x n k ∈ Icc (-1 : ℝ) 1)
    (hx_distinct : ∀ n, Function.Injective (x n))
    (ε : ℕ → ℝ)
    (hε_pos : ∀ n, 0 < ε n)
    (hε_lim : Tendsto ε atTop (nhds 0)) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) ∧
      ∀ p : ℕ → Polynomial ℝ,
        (∀ n, n ≥ 1 → ((p n).natDegree : ℝ) < (1 + ε n) * n) →
        (∀ n, ∀ k : Fin n, (p n).eval (x n k) = f (x n k)) →
        ∀ᵐ t ∂(volume.restrict (Icc (-1 : ℝ) 1)),
          ¬Tendsto (fun n => (p n).eval t) atTop (nhds (f t)) :=
  sorry

end Erdos1152
