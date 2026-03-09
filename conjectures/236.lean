import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Filter

noncomputable section

/--
For a natural number n, the number of representations n = p + 2^k
where p is prime and k ≥ 0.
-/
noncomputable def erdos236_f (n : ℕ) : ℕ :=
  Set.ncard {pk : ℕ × ℕ | pk.1.Prime ∧ n = pk.1 + 2 ^ pk.2}

/--
Erdős Problem #236 [Er55c, Er61, Er77c]:

Let f(n) count the number of solutions to n = p + 2^k for prime p and k ≥ 0.
Is it true that f(n) = o(log n)?

That is, does f(n) / log(n) → 0 as n → ∞?
-/
theorem erdos_problem_236 :
    Tendsto (fun n : ℕ => (erdos236_f n : ℝ) / Real.log n) atTop (nhds 0) :=
  sorry

end
