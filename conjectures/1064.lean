import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic

open Classical Nat Filter Finset

noncomputable section

/-!
# Erdős Problem #1064

Prove that φ(n) > φ(n - φ(n)) for almost all n, but that φ(n) < φ(n - φ(n))
for infinitely many n, where φ is Euler's totient function.

Reference: [Er80f]
https://www.erdosproblems.com/1064

Solved by Luca and Pomerance [LuPo02], who proved that the set where
φ(n) > φ(n - φ(n)) has density 1. Grytczuk, Luca, and Wójtowicz [GLW01]
had earlier shown that the set where φ(n) < φ(n - φ(n)) is infinite
(e.g., n = 15 · 2^k for any k ≥ 1).
-/

/-- Count of integers m ∈ {1, ..., N} satisfying predicate P. -/
noncomputable def countSat1064 (P : ℕ → Prop) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => P (n + 1))).card

/--
Erdős Problem #1064, Part (a):

φ(n) > φ(n - φ(n)) for almost all n. That is, the natural density of the set
{n : φ(n) > φ(n - φ(n))} is 1.

We require n > φ(n) (i.e., n ≥ 2) so that n - φ(n) is a valid natural number.
-/
theorem erdos_problem_1064a :
    Filter.Tendsto
      (fun N : ℕ =>
        (countSat1064 (fun n => n ≥ 2 ∧ n.totient > (n - n.totient).totient) (N + 1) : ℝ) /
          ((N + 1 : ℕ) : ℝ))
      atTop (nhds 1) :=
  sorry

/--
Erdős Problem #1064, Part (b):

φ(n) < φ(n - φ(n)) for infinitely many n.
-/
theorem erdos_problem_1064b :
    Set.Infinite {n : ℕ | n ≥ 2 ∧ n.totient < (n - n.totient).totient} :=
  sorry

end
