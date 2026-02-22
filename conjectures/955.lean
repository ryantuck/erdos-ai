import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic

open scoped Classical

noncomputable section

/-!
# Erdős Problem #955

Let s(n) = σ(n) - n = Σ_{d | n, d < n} d be the sum of proper divisors function.

If A ⊂ ℕ has density 0, then s⁻¹(A) must also have density 0.

A conjecture of Erdős, Granville, Pomerance, and Spiro [EGPS90]. It is possible
for s(A) to have positive density even if A has zero density (for example taking
A to be the product of two distinct primes). Erdős proved that there are sets A
of positive density such that s⁻¹(A) is empty.

Reference: [EGPS90]
https://www.erdosproblems.com/955

Tags: number theory
-/

/-- The sum of proper divisors function s(n) = Σ_{d | n, d < n} d. -/
def sumProperDivisors (n : ℕ) : ℕ := n.properDivisors.sum id

/-- A set A ⊆ ℕ has natural density zero if for every ε > 0, there exists N such
    that for all x ≥ N, the proportion of elements of A below x is less than ε. -/
def HasNaturalDensityZero (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ x : ℕ, x ≥ N →
    ((Finset.filter (· ∈ A) (Finset.range x)).card : ℝ) / (x : ℝ) < ε

/--
**Erdős Problem #955** [EGPS90]:

If A ⊆ ℕ has natural density zero, then so does s⁻¹(A) = {n ∈ ℕ : s(n) ∈ A},
where s is the sum of proper divisors function.
-/
theorem erdos_problem_955 (A : Set ℕ) (hA : HasNaturalDensityZero A) :
    HasNaturalDensityZero {n : ℕ | sumProperDivisors n ∈ A} :=
  sorry

end
