import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.Lemmas
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section

/--
A sequence of positive integers `a` has the **bounded perturbation irrationality
property** if for every bounded sequence of integers `b` with `a n + b n ≠ 0`
and `b n ≠ 0` for all `n`, the sum `∑ 1/(a n + b n)` is irrational.

This is Erdős's alternative definition of an 'irrationality sequence'
(see also problems #262 and #263).
-/
def BddPerturbIrrational (a : ℕ → ℕ) : Prop :=
  ∀ b : ℕ → ℤ, (∃ M : ℤ, ∀ n, |b n| ≤ M) →
    (∀ n, (a n : ℤ) + b n ≠ 0) →
    (∀ n, b n ≠ 0) →
    Irrational (∑' n, (1 : ℝ) / ((a n : ℝ) + (b n : ℤ)))

/--
Erdős Problem #264 [ErGr80, Er88c]:

Is `a_n = n!` an example of a sequence with the bounded perturbation irrationality
property? That is, for every bounded sequence of integers `b_n` with
`n! + b_n ≠ 0` and `b_n ≠ 0` for all `n`, is `∑ 1/(n! + b_n)` irrational?

Note: Kovač and Tao [KoTa24] proved that `a_n = 2^n` does NOT have this property,
so the original question about `2^n` is resolved negatively.
-/
theorem erdos_problem_264 :
    BddPerturbIrrational (fun n => n.factorial) :=
  sorry

end
