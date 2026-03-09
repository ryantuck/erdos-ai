import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/-- The set of numbers of the form a^k * b^l * c^m for nonneg exponents. -/
def smoothNumbers (a b c : ℕ) : Set ℕ :=
  { n | ∃ k l m : ℕ, n = a ^ k * b ^ l * c ^ m }

/-- A finite set of natural numbers is an antichain under divisibility:
    no element divides any other distinct element. -/
def DivisibilityAntichain (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ∣ y → x = y

/-- A set S ⊆ ℕ is d-complete if every sufficiently large natural number
    can be written as the sum of distinct elements of S, no one of which
    divides another. -/
def IsDComplete (S : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Finset ℕ, ↑s ⊆ S ∧ DivisibilityAntichain s ∧ s.sum id = n

/--
Erdős Problem #123 [Er92b, ErLe96, Er97, Er97e] — OPEN ($250)

Let a, b, c ≥ 1 be three integers which are pairwise coprime. Is every
sufficiently large integer the sum of distinct integers of the form
a^k * b^l * c^m (k, l, m ≥ 0), none of which divide any other?

Equivalently, is the set {a^k * b^l * c^m : k, l, m ≥ 0} always d-complete
when a, b, c are pairwise coprime?

Erdős and Lewin proved the case a=3, b=5, c=7, along with several cases
with a=2, b=5. Further cases have been verified by Ma–Chen and Chen–Yu.
-/
theorem erdos_problem_123
    (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    IsDComplete (smoothNumbers a b c) :=
  sorry
