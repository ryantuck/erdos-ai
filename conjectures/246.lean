import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

/-!
# Erdős Problem #246

Let (a,b) = 1 with a, b ≥ 2. The set {a^k · b^l : k, l ≥ 0} is complete — that
is, every sufficiently large positive integer is the sum of distinct integers of
the form a^k · b^l.

Proved by Birch [Bi59]. This also follows from a later more general result
of Cassels [Ca60] (see [254]).

Davenport observed that this is still true even with l ≪_{a,b} 1. Hegyvári
[He00b] gave an explicit upper bound for this threshold.
-/

/-- The set of all natural numbers of the form a^k · b^l for k, l ≥ 0. -/
def twoPowerSet (a b : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k l : ℕ, n = a ^ k * b ^ l}

/-- A set S ⊆ ℕ is complete if every sufficiently large natural number
    can be expressed as a sum of distinct elements of S. -/
def IsComplete (S : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N < n →
    ∃ F : Finset ℕ, (↑F ⊆ S) ∧ ∑ x ∈ F, x = n

/--
Erdős Problem #246 [Er61] (proved by Birch [Bi59]):
Let a, b ≥ 2 with gcd(a, b) = 1. Then every sufficiently large positive integer
is the sum of distinct integers of the form a^k · b^l with k, l ≥ 0.

This also follows from a later more general result of Cassels [Ca60] (see [254]).
-/
theorem erdos_problem_246 :
    ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → Nat.Coprime a b →
      IsComplete (twoPowerSet a b) :=
  sorry
