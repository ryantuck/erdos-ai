import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Polynomial Finset BigOperators

/--
Erdős Problem #283 [ErGr80, p.32]:

Let p : ℤ → ℤ be a polynomial with positive leading coefficient such that
there is no integer d ≥ 2 dividing p(n) for all n ≥ 1. Is it true that for
all sufficiently large m, there exist distinct positive integers n₁ < ⋯ < nₖ
such that
  1/n₁ + ⋯ + 1/nₖ = 1
and
  p(n₁) + ⋯ + p(nₖ) = m?

Graham proved this when p(x) = x. Alekseyev proved this when p(x) = x².
-/
theorem erdos_problem_283
    (p : ℤ[X])
    (hlead : 0 < p.leadingCoeff)
    (hgcd : ¬∃ d : ℤ, 2 ≤ d ∧ ∀ n : ℤ, 1 ≤ n → d ∣ p.eval n) :
    ∃ M : ℤ, ∀ m : ℤ, M ≤ m →
      ∃ S : Finset ℕ,
        (∀ i ∈ S, 0 < i) ∧
        (∑ i ∈ S, (1 : ℚ) / (i : ℚ)) = 1 ∧
        (∑ i ∈ S, p.eval (i : ℤ)) = m :=
  sorry
