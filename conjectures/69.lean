import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped Topology

/--
Erdős Problem #69 [Er68d, ErGr80, Er88c, Er90, Er97f]:

Is the sum ∑_{n≥2} ω(n)/2ⁿ irrational, where ω(n) counts the number of
distinct prime divisors of n?

Tao observed that this equals ∑_p 1/(2^p - 1). This was proved to be
irrational unconditionally by Tao and Teräväinen [TaTe25].
-/
theorem erdos_problem_69 :
    Irrational (∑' (n : ℕ), if n < 2 then (0 : ℝ)
      else (n.primeFactors.card : ℝ) / (2 : ℝ) ^ n) :=
  sorry
