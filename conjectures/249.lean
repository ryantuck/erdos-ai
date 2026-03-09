import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped Topology

/--
Erdős Problem #249 [ErGr80, Er88c]:

Is the sum ∑_{n≥1} φ(n) / 2ⁿ irrational, where φ is Euler's totient function?

The decimal expansion of this sum is A256936 on the OEIS.
-/
theorem erdos_problem_249 :
    Irrational (∑' (n : ℕ), (Nat.totient n : ℝ) / 2 ^ n) :=
  sorry
