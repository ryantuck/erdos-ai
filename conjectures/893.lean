import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Nat Filter

noncomputable section

/--
The function f(n) = Σ_{k=1}^{n} τ(2^k - 1), where τ is the number-of-divisors function.
-/
noncomputable def erdos893_f (n : ℕ) : ℕ :=
  (Finset.range n).sum fun k => (2 ^ (k + 1) - 1).divisors.card

/--
Erdős Problem #893 [Er98]:

If τ(n) counts the divisors of n then let f(n) = Σ_{1≤k≤n} τ(2^k - 1).
Does f(2n)/f(n) tend to a limit?

Erdős says that 'probably there is no simple asymptotic formula for f(n) since
f(n) increases too fast'. Kovač and Luca [KoLu25] showed that
lim sup_{n→∞} f(2n)/f(n) = ∞, and provide evidence that
lim_{n→∞} f(2n)/f(n) = ∞.
-/
theorem erdos_problem_893 :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => (erdos893_f (2 * n) : ℝ) / (erdos893_f n : ℝ))
      Filter.atTop (nhds L) :=
  sorry

end
