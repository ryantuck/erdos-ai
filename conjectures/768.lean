import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Finset.Basic

open Nat Real Filter Classical

noncomputable section

/-!
# Erdős Problem #768

Let A ⊂ ℕ be the set of n such that for every prime p ∣ n there exists some
d ∣ n with d > 1 such that d ≡ 1 (mod p). Is it true that there exists some
constant c > 0 such that for all large N,

  |A ∩ [1,N]| / N = exp(-(c + o(1)) √(log N) · log log N)?

Erdős could prove that there exists some constant c > 0 such that for all large N,

  exp(-c √(log N) log log N) ≤ |A ∩ [1,N]| / N

and

  |A ∩ [1,N]| / N ≤ exp(-(1+o(1)) √(log N · log log N)).

Erdős asked about this because |A ∩ [1,N]| provides an upper bound for the
number of integers n ≤ N for which there is a non-cyclic simple group of order n.

Reference: [Er74b]
https://www.erdosproblems.com/768
-/

/-- An integer n is in the set A if for every prime p dividing n, there exists
    some divisor d > 1 of n with d ≡ 1 (mod p). -/
def erdos768_inA (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → ∃ d : ℕ, d > 1 ∧ d ∣ n ∧ d % p = 1

/-- Count of integers in {1, ..., N} belonging to the set A. -/
noncomputable def erdos768_count (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => erdos768_inA (n + 1))).card

/--
Erdős Problem #768 [Er74b]:

There exists c > 0 such that
  |A ∩ [1,N]| / N = exp(-(c + o(1)) √(log N) · log log N).

Formalized as: there exists c > 0 such that
  -log(|A ∩ [1,N]| / N) / (√(log N) · log(log N)) → c as N → ∞.
-/
theorem erdos_problem_768 :
    ∃ c : ℝ, c > 0 ∧
    Tendsto
      (fun N : ℕ =>
        -Real.log ((erdos768_count N : ℝ) / (N : ℝ)) /
          (Real.sqrt (Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ))))
      atTop (nhds c) :=
  sorry

end
