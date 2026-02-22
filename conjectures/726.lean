import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Real Filter

noncomputable section

/-!
# Erdős Problem #726

As n → ∞ ranges over integers,
  ∑_{p ≤ n} 1_{n ∈ (p/2, p) (mod p)} · (1/p) ~ (log log n) / 2.

A conjecture of Erdős, Graham, Ruzsa, and Straus [EGRS75]. By n ∈ (p/2, p) (mod p)
we mean n ≡ r (mod p) for some integer r with p/2 < r < p. Equivalently, the
condition holds when 2 * (n % p) > p.

For comparison, the classical estimate of Mertens states that
  ∑_{p ≤ n} 1/p ~ log log n.

https://www.erdosproblems.com/726
-/

/-- The weighted sum of 1/p over primes p ≤ n for which n mod p lies in (p/2, p),
    i.e., 2 * (n % p) > p. This captures the condition n ≡ r (mod p) for some
    integer r with p/2 < r < p. -/
noncomputable def erdos726_sum (n : ℕ) : ℝ :=
  ((Finset.range (n + 1)).filter Nat.Prime).sum
    (fun p => if 2 * (n % p) > p then (1 : ℝ) / (p : ℝ) else 0)

/--
Erdős Problem #726 [EGRS75]:

As n → ∞,
  ∑_{p ≤ n} 1_{n ∈ (p/2, p) (mod p)} · (1/p) ~ (log log n) / 2.

Stated as: the ratio of the sum to (log log n)/2 tends to 1.
-/
theorem erdos_problem_726 :
    Tendsto (fun n : ℕ => erdos726_sum n / (Real.log (Real.log (n : ℝ)) / 2))
      atTop (nhds 1) :=
  sorry

end
