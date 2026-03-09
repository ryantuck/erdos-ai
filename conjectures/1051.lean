import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

/--
Erdős Problem #1051 [ErGr80,p.64] [Er88c,p.106]:

Is it true that if 1 ≤ a₁ < a₂ < ⋯ is a sequence of integers with
  liminf aₙ^{1/2ⁿ} > 1
then
  ∑ 1/(aₙ · aₙ₊₁)
is irrational?

Solved in the affirmative by Aletheia [Fe26].
-/
theorem erdos_problem_1051
    (a : ℕ → ℕ)
    (ha_pos : ∀ n, 1 ≤ a n)
    (ha_strict_mono : StrictMono a)
    (ha_growth : atTop.liminf (fun n => ((a n : ℝ) ^ ((2 : ℝ) ^ (n : ℝ))⁻¹)) > 1) :
    Irrational (∑' n, (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))) :=
  sorry
