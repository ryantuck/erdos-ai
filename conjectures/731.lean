import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Filter Real

noncomputable section

/-!
# Erdős Problem #731

Find some reasonable function f(n) such that, for almost all integers n,
the least integer m such that m ∤ C(2n, n) satisfies m ~ f(n).

A problem of Erdős, Graham, Ruzsa, and Straus [EGRS75], who say it is
'not hard to show that', for almost all n, the minimal such m satisfies
  m = exp((log n)^{1/2 + o(1)}).

Tags: number theory, binomial coefficients
-/

/-- The least integer m ≥ 2 that does not divide C(2n, n). -/
noncomputable def leastNonDivisorCentralBinom (n : ℕ) : ℕ :=
  sInf {m : ℕ | 2 ≤ m ∧ ¬(m ∣ Nat.choose (2 * n) n)}

/--
Erdős Problem #731 [EGRS75]:

For almost all n, the least m ≥ 2 not dividing C(2n, n) satisfies
  m = exp((log n)^{1/2 + o(1)}),
i.e., for every ε > 0, the natural density of integers n where the
least non-divisor of C(2n, n) falls outside the interval
  [exp((log n)^{1/2 - ε}), exp((log n)^{1/2 + ε})]
is zero.

The open problem asks to find a precise closed-form function f(n) such
that m ~ f(n) for almost all n.
-/
theorem erdos_problem_731 (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun x : ℕ =>
      (((Finset.Icc 1 x).filter (fun n : ℕ =>
        let m : ℝ := (leastNonDivisorCentralBinom n : ℝ)
        ¬(exp ((log (↑n : ℝ)) ^ ((1 : ℝ) / 2 - ε)) ≤ m ∧
          m ≤ exp ((log (↑n : ℝ)) ^ ((1 : ℝ) / 2 + ε))))).card : ℝ) / (↑x : ℝ))
      atTop (nhds 0) :=
  sorry

end
