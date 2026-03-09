import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat

open Nat Filter Finset Asymptotics
open scoped Topology

noncomputable section

namespace Erdos394

/--
For k, n : ℕ, the least positive m such that n ∣ m(m+1)(m+2)⋯(m+k-1).
-/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }

/--
Erdős Problem #394, Part (a) [ErHa78, ErGr80]:

Is it true that ∑_{n ≤ x} t₂(n) ≪ x² / (log x)^c for some c > 0?
-/
theorem erdos_problem_394a :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ))) =O[atTop]
      (fun x : ℝ => x ^ 2 / (Real.log x) ^ c) :=
  sorry

/--
Erdős Problem #394, Part (b) [ErHa78, ErGr80]:

Is it true that, for k ≥ 2,
  ∑_{n ≤ x} t_{k+1}(n) = o(∑_{n ≤ x} t_k(n))?
-/
theorem erdos_problem_394b :
    ∀ k : ℕ, 2 ≤ k →
      (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, (t (k + 1) n : ℝ))) =o[atTop]
      (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, (t k n : ℝ))) :=
  sorry

end Erdos394

end
