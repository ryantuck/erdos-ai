import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter

noncomputable section

/-- A strictly increasing sequence of positive integers is an irrationality sequence
    if for every sequence of positive integers t, the sum ∑ 1/(tₙ · aₙ) is irrational. -/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (∀ n, 0 < a n) ∧
  ∀ t : ℕ → ℕ, (∀ n, 0 < t n) →
    Irrational (∑' n, (1 : ℝ) / ((t n : ℝ) * (a n : ℝ)))

/--
Erdős Problem #262 [ErGr80, Er88c]:
Suppose a₁ < a₂ < ⋯ is a sequence of positive integers such that for all
sequences of positive integers tₙ, the sum ∑ 1/(tₙaₙ) is irrational
(i.e., a is an irrationality sequence). How slowly can aₙ grow?

An example of such a sequence is aₙ = 2^{2^n} (Erdős [Er75c]), while
a non-example is aₙ = n!.

Hančl [Ha91] proved that any irrationality sequence must satisfy
  limsup_{n→∞} (log₂ log₂ aₙ) / n ≥ 1,
i.e., for all c < 1, log₂(log₂(aₙ)) > cn for infinitely many n.
-/
theorem erdos_problem_262
    (a : ℕ → ℕ) (ha : IsIrrationalitySequence a)
    (c : ℝ) (hc : c < 1) :
    Filter.Frequently (fun (n : ℕ) => c * (↑n : ℝ) < Real.logb 2 (Real.logb 2 (↑(a n) : ℝ))) atTop :=
  sorry

end
