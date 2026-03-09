import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat

/--
The prime gap at index n: d_n = p_{n+1} - p_n.
-/
noncomputable def primeGap (n : ℕ) : ℕ :=
  nth Nat.Prime (n + 1) - nth Nat.Prime n

/--
Erdős Problem #218 [Er55c, Er57, Er61, Er65b, Er85c]:

Let d_n = p_{n+1} - p_n. The set of n such that d_{n+1} ≥ d_n has density 1/2,
and similarly for d_{n+1} ≤ d_n. Furthermore, there are infinitely many n
such that d_{n+1} = d_n.

The density statement means: #{n ≤ N : d_{n+1} ≥ d_n} / N → 1/2 as N → ∞,
and similarly for ≤.
-/
theorem erdos_problem_218_increasing :
    Filter.Tendsto
      (fun N : ℕ => (Finset.filter (fun n => decide (primeGap (n + 1) ≥ primeGap n) = true)
        (Finset.range N)).card / (N : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) :=
  sorry

/-- The set of n such that d_{n+1} ≤ d_n has natural density 1/2. -/
theorem erdos_problem_218_decreasing :
    Filter.Tendsto
      (fun N : ℕ => (Finset.filter (fun n => decide (primeGap (n + 1) ≤ primeGap n) = true)
        (Finset.range N)).card / (N : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) :=
  sorry

/-- There are infinitely many n such that d_{n+1} = d_n. -/
theorem erdos_problem_218_equal :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ primeGap (n + 1) = primeGap n :=
  sorry
