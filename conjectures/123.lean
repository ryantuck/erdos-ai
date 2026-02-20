import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

/-- The set of natural numbers of the form a^k * b^l * c^m for k, l, m ≥ 0. -/
def threePowerSet (a b c : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k l m : ℕ, n = a ^ k * b ^ l * c ^ m}

/-- A finite set F of natural numbers is an antichain under divisibility
    if no element divides any other distinct element. -/
def IsAntichainDvd (F : Finset ℕ) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ¬(x ∣ y)

/-- A set S ⊆ ℕ is d-complete if every sufficiently large natural number
    can be expressed as a sum of distinct elements of S forming an antichain
    under divisibility (no summand divides any other). -/
def IsDComplete (S : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N < n →
    ∃ F : Finset ℕ, (↑F ⊆ S) ∧ IsAntichainDvd F ∧ ∑ x ∈ F, x = n

/--
Erdős Problem #123 [Er92b, ErLe96, Er97, Er97e] — OPEN ($250)

Let a, b, c ≥ 1 be three integers which are pairwise coprime. Is every
sufficiently large integer the sum of distinct integers of the form
a^k * b^l * c^m (k, l, m ≥ 0), none of which divide any other?

Equivalently: is the set {a^k * b^l * c^m : k, l, m ≥ 0} d-complete for
every triple (a, b, c) of pairwise coprime positive integers? A set S is
d-complete if every sufficiently large integer is the sum of distinct
elements from S, no one of which divides another.

Known cases:
  - (a, b, c) = (3, 5, 7), and a = 2, b = 5, c ∈ {7, 11, 13, 17, 19}
    (Erdős-Lewin [ErLe96])
  - a = 2, b = 5, c ∈ {9, 21, 23, 27, 29, 31} and more (Ma-Chen [MaCh16])
  - a=2,b=5 for 3≤c≤87; a=2,b=7 for 3≤c≤33; a=3,b=5 for 2≤c≤14
    (Chen-Yu [ChYu23b])
-/
theorem erdos_problem_123 :
    ∀ a b c : ℕ, 1 ≤ a → 1 ≤ b → 1 ≤ c →
      Nat.Coprime a b → Nat.Coprime b c → Nat.Coprime a c →
      IsDComplete (threePowerSet a b c) :=
  sorry
