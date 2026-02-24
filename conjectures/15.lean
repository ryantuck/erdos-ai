import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Nat BigOperators

noncomputable section

/--
Erdős Problem #15:

Is it true that the alternating series
  ∑_{n=1}^∞ (-1)^n · n/pₙ
converges, where pₙ denotes the n-th prime?

This is an open problem. Tao has proved convergence assuming a strong form
of the Hardy–Littlewood prime tuples conjecture.

We state the conjecture as: the sequence of partial sums
  S_N = ∑_{n=1}^N (-1)^n · n/pₙ
converges to a real limit L.

Using 0-indexed `Nat.nth Nat.Prime`, the n-th term (n : ℕ, 0-indexed) is
  (-1)^(n+1) · (n+1) / (Nat.nth Nat.Prime n : ℝ),
which corresponds to the 1-indexed term (-1)^(n+1) · (n+1)/p_{n+1}.
-/
theorem erdos_problem_15 :
    ∃ L : ℝ,
      Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N,
          (-1 : ℝ) ^ (n + 1) * ((n + 1 : ℝ) / (Nat.nth Nat.Prime n : ℝ)))
        atTop (nhds L) :=
  sorry

end
