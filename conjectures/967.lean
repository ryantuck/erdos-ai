import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Real.Basic

open Complex

noncomputable section

/--
Erdős Problem #967 (Disproved by Yip [Yi25]):

Let 1 < a₁ < a₂ < ⋯ be a strictly increasing sequence of integers with
∑ 1/aₖ < ∞. Erdős and Ingham [ErIn64] asked whether it is necessarily true
that for every real t,
  1 + ∑ₖ aₖ^{-(1+it)} ≠ 0.

Yip proved that for any real t ≠ 0, there exists such a sequence satisfying
  1 + ∑ₖ aₖ^{-(1+it)} = 0.

It remains open whether this holds for every finite sequence of integers.
-/
theorem erdos_problem_967 :
    ∀ t : ℝ, t ≠ 0 →
      ∃ a : ℕ → ℕ,
        StrictMono a ∧
        (∀ i, 2 ≤ a i) ∧
        Summable (fun i => (1 : ℝ) / (a i : ℝ)) ∧
        1 + (∑' k, (1 : ℂ) / ((a k : ℂ) ^ ((1 : ℂ) + ↑t * I))) = 0 :=
  sorry

end
