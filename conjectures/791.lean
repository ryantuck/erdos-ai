import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open scoped Pointwise

noncomputable section

/-!
# Erdős Problem #791

Let g(n) be the minimal size of a set A ⊆ {0, …, n} such that {0, …, n} ⊆ A + A
(i.e., A is a finite additive 2-basis for {0, …, n}). Estimate g(n).
In particular, is it true that g(n) ~ 2√n?

A problem of Erdős [Er73], building on work of Rohrbach [Ro37].

Rohrbach [Ro37] proved (2 + c)·n ≤ g(n)² ≤ 4·n for some small c > 0.

The current best-known bounds are:
  (2.181… + o(1))·n ≤ g(n)² ≤ (3.458… + o(1))·n.

The lower bound is due to Yu [Yu15], the upper bound to Kohonen [Ko17].
The disproof of g(n) ~ 2√n was accomplished by Mrose [Mr79], who showed
g(n)² ≤ (7/2)·n.

https://www.erdosproblems.com/791
-/

/-- `additiveBasesMinSize n` is the minimum cardinality of a set A ⊆ {0, …, n}
    such that every element of {0, …, n} can be written as a sum of two elements
    of A (a finite additive 2-basis). This is the function g(n) in Erdős Problem #791. -/
noncomputable def additiveBasesMinSize (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℕ, A.card = k ∧
    A ⊆ Finset.range (n + 1) ∧ Finset.range (n + 1) ⊆ A + A}

/--
Erdős Problem #791 — Best known lower bound (Yu [Yu15]):

For all ε > 0, for sufficiently large n,
  g(n)² ≥ (2181/1000 - ε) · n.

The constant 2181/1000 approximates 2.181…
-/
theorem erdos_problem_791_lower :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ((2181 : ℝ) / 1000 - ε) * (n : ℝ) ≤ ((additiveBasesMinSize n : ℝ)) ^ 2 :=
  sorry

/--
Erdős Problem #791 — Best known upper bound (Kohonen [Ko17]):

For all ε > 0, for sufficiently large n,
  g(n)² ≤ (3459/1000 + ε) · n.

The constant 3459/1000 approximates 3.458…
-/
theorem erdos_problem_791_upper :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ((additiveBasesMinSize n : ℝ)) ^ 2 ≤ ((3459 : ℝ) / 1000 + ε) * (n : ℝ) :=
  sorry

/--
Erdős Problem #791 — Main open question:

Determine the value of lim_{n → ∞} g(n)² / n, if it exists.
Currently known to lie in the interval [2.181…, 3.458…].

Formalized as: there exists c > 0 such that g(n)² = (c + o(1)) · n.
-/
theorem erdos_problem_791 :
    ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      |((additiveBasesMinSize n : ℝ)) ^ 2 - c * (n : ℝ)| ≤ ε * (n : ℝ) :=
  sorry

end
