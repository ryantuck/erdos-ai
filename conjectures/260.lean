import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter

/--
Erdős Problem #260:
Let a₁ < a₂ < ⋯ be a strictly increasing sequence of natural numbers such
that aₙ/n → ∞. Is the sum ∑ₙ aₙ/2^(aₙ) irrational?
-/
theorem erdos_problem_260_conjecture :
  ∀ a : ℕ → ℕ,
    StrictMono a →
    Tendsto (fun n => (a n : ℝ) / (n : ℝ)) atTop atTop →
    Irrational (∑' n, (a n : ℝ) / (2 : ℝ) ^ (a n)) :=
sorry
