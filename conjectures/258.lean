import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Filter Finset BigOperators

/--
Erdős Problem #258 [ErGr80, Er88c]:

Let a₁, a₂, … be a sequence of positive integers with aₙ → ∞. Is
  ∑ₙ τ(n) / (a₁ · a₂ · ⋯ · aₙ)
irrational, where τ(n) is the number of divisors of n?

Erdős and Straus proved this when aₙ is monotone nondecreasing.
-/
theorem erdos_problem_258 :
  ∀ a : ℕ → ℕ,
    (∀ n, 0 < a n) →
    Tendsto (fun n => (a n : ℝ)) atTop atTop →
    Irrational (∑' n, ((Nat.divisors (n + 1)).card : ℝ) /
      (∏ i ∈ range (n + 1), (a i : ℝ))) :=
sorry
