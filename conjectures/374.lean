import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Filter.AtTopBot.Basic

open scoped BigOperators
open Filter Classical

/--
There exists a set of `k` distinct natural numbers with maximum element `m`
whose product of factorials is a perfect square.
Formally: there exist a₁ < ··· < aₖ = m with a₁!···aₖ! a square.
-/
def HasFactorialSquareSeq (m : ℕ) (k : ℕ) : Prop :=
  ∃ (s : Finset ℕ), s.card = k ∧ k ≥ 2 ∧ m ∈ s ∧
    (∀ x ∈ s, x ≤ m) ∧
    IsSquare (∏ x ∈ s, Nat.factorial x)

/--
`m ∈ D_k`: the minimal factorial-square sequence length for `m` is exactly `k`.
F(m) = k where F(m) is the minimal k ≥ 2 such that there exist
a₁ < ··· < aₖ = m with a₁!···aₖ! a perfect square.
-/
def IsInD (k : ℕ) (m : ℕ) : Prop :=
  HasFactorialSquareSeq m k ∧ ∀ j, j < k → ¬HasFactorialSquareSeq m j

/--
Erdős Problem #374 [ErGr76][ErGr80]:

For m ∈ ℕ, let F(m) be the minimal k ≥ 2 such that there exist a₁ < ··· < aₖ = m
with a₁!···aₖ! a perfect square. Let Dₖ = {m : F(m) = k}.

Conjecture: |D₆ ∩ {1,...,n}| ≫ n.

That is, there exists c > 0 such that for all sufficiently large n,
the count of m ≤ n with F(m) = 6 is at least c · n.
-/
theorem erdos_problem_374 :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ n : ℕ in atTop,
        (((Finset.Icc 1 n).filter (fun m => IsInD 6 m)).card : ℝ) ≥ c * (n : ℝ) :=
  sorry
