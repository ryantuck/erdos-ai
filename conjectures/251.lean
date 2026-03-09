import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped Topology

/--
Erdős Problem #251 [Er58b, ErGr80, Er88c]:

Is the sum ∑_{n≥0} p_n / 2ⁿ irrational, where p_n is the nth prime
(0-indexed, so p₀ = 2, p₁ = 3, p₂ = 5, ...)?
-/
theorem erdos_problem_251 :
    Irrational (∑' (n : ℕ), (Nat.nth Nat.Prime n : ℝ) / 2 ^ n) :=
  sorry
