import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/--
A choice of residue classes for primes p ≤ x covers [1, y] if every
integer n ∈ {1, ..., y} is congruent to a(p) mod p for some prime p ≤ x.
This captures the covering system used in the Jacobsthal function.
-/
def PrimeCovering (x y : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ y → ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ n % p = a p % p

/--
Erdős Problem #687 (weak form): Y(x) = o(x²).
Let Y(x) be the maximal y such that there exists a choice of congruence
classes a_p for all primes p ≤ x such that every integer in [1,y] is
congruent to at least one of the a_p (mod p). Then Y(x) = o(x²).
-/
theorem erdos_problem_687_weak :
    ∀ ε : ℝ, ε > 0 → ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
    ∀ (a : ℕ → ℕ) (y : ℕ), PrimeCovering x y a →
    (y : ℝ) < ε * (x : ℝ) ^ 2 :=
  sorry

/--
Erdős Problem #687 (strong form): Y(x) ≪ x^{1+o(1)}.
For every ε > 0, for all sufficiently large x, any covering of [1,y]
by residue classes of primes ≤ x satisfies y ≤ x^{1+ε}.
-/
theorem erdos_problem_687_strong :
    ∀ ε : ℝ, ε > 0 → ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
    ∀ (a : ℕ → ℕ) (y : ℕ), PrimeCovering x y a →
    (y : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) + ε) :=
  sorry
