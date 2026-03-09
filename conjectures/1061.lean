import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

open scoped ArithmeticFunction.sigma

/--
Count the number of pairs (a, b) with a, b ≥ 1 and a + b ≤ n such that
σ(a) + σ(b) = σ(a + b).
-/
noncomputable def countSigmaAdditivePairs (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun p => p.1 + p.2 ≤ n ∧ σ 1 p.1 + σ 1 p.2 = σ 1 (p.1 + p.2))).card

/--
Erdős Problem #1061 [Gu04]:

How many solutions are there to σ(a) + σ(b) = σ(a + b) with a + b ≤ x,
where σ is the sum of divisors function? Is it ∼ cx for some constant c > 0?
-/
theorem erdos_problem_1061 :
    ∃ c : ℝ, 0 < c ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun n => (countSigmaAdditivePairs n : ℝ))
        (fun n => c * (n : ℝ)) :=
  sorry
