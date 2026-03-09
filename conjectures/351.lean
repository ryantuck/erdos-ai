import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Defs

open Polynomial Finset BigOperators

/--
A set of rationals is **strongly complete** if, after removing any finite subset,
the finite subset sums of the remaining elements contain all sufficiently large
integers.
-/
def StronglyComplete (A : Set ℚ) : Prop :=
  ∀ B : Finset ℚ, ∃ M : ℤ, ∀ m : ℤ, M ≤ m →
    ∃ S : Finset ℚ,
      (↑S : Set ℚ) ⊆ A \ ↑B ∧
      (∑ x ∈ S, x) = ↑m

/--
Erdős Problem #351 [ErGr80, p.58]:

Let p(x) ∈ ℚ[x]. Is it true that A = { p(n) + 1/n : n ∈ ℕ, n ≥ 1 } is
strongly complete, in the sense that for any finite set B, the set of finite
subset sums of A \ B contains all sufficiently large integers?

Graham proved this when p(x) = x.
-/
theorem erdos_problem_351 (p : ℚ[X]) :
    StronglyComplete { q : ℚ | ∃ n : ℕ, 0 < n ∧ q = p.eval (↑n : ℚ) + 1 / (↑n : ℚ) } :=
  sorry
