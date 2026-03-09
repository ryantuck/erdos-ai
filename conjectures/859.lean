import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open BigOperators Finset Filter Real

noncomputable section

/--
The integer `t` is representable as a sum of distinct divisors of `n`:
some subset of the divisors of `n` sums to `t`.
-/
def IsSumOfDistinctDivisors (n t : ℕ) : Prop :=
  ∃ S ∈ n.divisors.powerset, S.sum id = t

instance (n t : ℕ) : Decidable (IsSumOfDistinctDivisors n t) :=
  inferInstanceAs (Decidable (∃ S ∈ n.divisors.powerset, S.sum id = t))

/--
The natural density of the set of natural numbers satisfying a decidable predicate,
defined as the limit of |{m ≤ N : P m}| / N as N → ∞.
-/
def naturalDensity (P : ℕ → Prop) [DecidablePred P] : ℝ :=
  limUnder atTop (fun N : ℕ =>
    ((Finset.Icc 1 N).filter (fun m => P m)).card / (N : ℝ))

/--
Erdős Problem #859 [Er70]:

Let t ≥ 1 and let d_t be the density of the set of integers n ∈ ℕ for
which t can be represented as the sum of distinct divisors of n. Do there
exist constants c₁, c₂ > 0 such that d_t ~ c₁ / (log t)^{c₂} as t → ∞?

Erdős [Er70] proved that d_t always exists and that there exist constants
c₃, c₄ > 0 such that 1/(log t)^{c₃} < d_t < 1/(log t)^{c₄}.
-/
theorem erdos_problem_859 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      Tendsto
        (fun t : ℕ =>
          naturalDensity (fun n => IsSumOfDistinctDivisors n t) /
            (c₁ / (Real.log t) ^ c₂))
        atTop (nhds 1) :=
  sorry

end
