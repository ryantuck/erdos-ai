import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Real.Irrational

open Nat ArithmeticFunction BigOperators

/--
The divisor power sum function σ_k(n) = ∑_{d ∣ n} d^k.
-/
noncomputable def sigmaFun (k : ℕ) (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d ^ k

/--
Erdős Problem #252 [ErGr80,p.62] [Er88c,p.102]:

Let k ≥ 1 and σ_k(n) = ∑_{d ∣ n} d^k. Is
  ∑_{n=0}^∞ σ_k(n) / n!
irrational?

This is known for 1 ≤ k ≤ 4. The cases k = 1, 2 are reasonably
straightforward (Erdős, 1952). The case k = 3 was proved independently by
Schlage-Puchta (2006) and Friedlander–Luca–Stoiciu (2007). The case k = 4
was proved by Pratt (2022). It is known for all k ≥ 1 conditional on
Schinzel's conjecture or Dickson's conjecture.
-/
theorem erdos_problem_252 (k : ℕ) (hk : 1 ≤ k) :
    Irrational (∑' n : ℕ, (sigmaFun k n : ℝ) / (n ! : ℝ)) :=
  sorry
