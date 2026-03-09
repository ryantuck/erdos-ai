import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped Topology

/--
Erdős Problem #250 [ErGr80, Er88c] (PROVED):

Is the sum ∑_{n≥1} σ(n) / 2ⁿ irrational, where σ(n) is the sum of divisors
function?

The answer is yes, as shown by Nesterenko [Ne96].
-/
theorem erdos_problem_250 :
    Irrational (∑' (n : ℕ), (((Nat.divisors n).sum id : ℕ) : ℝ) / 2 ^ n) :=
  sorry
