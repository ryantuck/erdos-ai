import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat ArithmeticFunction Filter Real

/--
The sum of divisors function σ(n) = ∑_{d ∣ n} d.
-/
noncomputable def sumDivisors (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/--
Iterated sum of divisors: σ_1(n) = σ(n) and σ_k(n) = σ(σ_{k-1}(n)).
-/
noncomputable def iteratedSigma : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => sumDivisors (iteratedSigma k n)

/--
Erdős Problem #410 [ErGr80]:

Let σ₁(n) = σ(n), the sum of divisors function, and σₖ(n) = σ(σₖ₋₁(n)).
Is it true that for all n ≥ 2,
  lim_{k → ∞} σₖ(n)^{1/k} = ∞?
-/
theorem erdos_problem_410 (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun k => ((iteratedSigma k n : ℝ) ^ ((1 : ℝ) / (k : ℝ)) : ℝ)) atTop atTop :=
  sorry
