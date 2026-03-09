import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

noncomputable section

/--
A sequence of positive integers `a` is an **irrationality sequence** if for every
sequence of positive integers `b` with `b n / a n → 1`, the sum `∑ 1 / b n` is
irrational.
-/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  ∀ b : ℕ → ℕ, (∀ n, 0 < b n) →
    Tendsto (fun n => (b n : ℝ) / (a n : ℝ)) atTop (nhds 1) →
    Irrational (∑' n, (1 : ℝ) / (b n : ℝ))

/--
Erdős Problem #263a [ErGr80, Er88c]:

Is `a_n = 2^{2^n}` an irrationality sequence? That is, for every sequence of
positive integers `b_n` with `b_n / 2^{2^n} → 1`, is `∑ 1/b_n` irrational?
-/
theorem erdos_problem_263a :
    IsIrrationalitySequence (fun n => 2 ^ 2 ^ n) :=
  sorry

/--
Erdős Problem #263b [ErGr80, Er88c]:

Must every irrationality sequence satisfy `a_n^{1/n} → ∞`? That is, if `a` is
an irrationality sequence (of positive integers), then for every `C > 0`, we
eventually have `a n > C ^ n`.
-/
theorem erdos_problem_263b
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hIrr : IsIrrationalitySequence a) :
    Tendsto (fun n => ((a n : ℝ)) ^ ((1 : ℝ) / (n : ℝ))) atTop atTop :=
  sorry

end
