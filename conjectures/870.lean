import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card

open Real

noncomputable section

/-!
# Erdős Problem #870

Let k ≥ 3 and A be an additive basis of order k. Does there exist a constant
c = c(k) > 0 such that if r(n) ≥ c log n for all large n then A must contain
a minimal basis of order k?

Here r(n) counts the number of representations of n as the sum of at most k
elements from A.

A question of Erdős and Nathanson [ErNa88]. Erdős and Nathanson [ErNa79]
proved this for k = 2 when 1_A ∗ 1_A(n) > (log(4/3))⁻¹ log n for all large n.

Härtter [Ha56] and Nathanson [Na74] proved that there exist additive bases
which do not contain any minimal additive bases.

See also problem #868.
-/

/-- A set A ⊆ ℕ is an additive basis of order k if every sufficiently large
    natural number can be represented as a sum of at most k elements of A
    (with repetition allowed). -/
def IsAdditiveBasis (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ (l : List ℕ), l.length ≤ k ∧ (∀ x ∈ l, x ∈ A) ∧ l.sum = n

/-- A set A is a minimal additive basis of order k if it is a basis of order k,
    but removing any single element makes it no longer a basis of order k. -/
def IsMinimalAdditiveBasis (A : Set ℕ) (k : ℕ) : Prop :=
  IsAdditiveBasis A k ∧ ∀ a ∈ A, ¬ IsAdditiveBasis (A \ {a}) k

/-- The number of representations of n as a sum of at most k elements from A.
    A representation is a non-decreasing list of elements of A with length at
    most k summing to n. Using non-decreasing lists gives a canonical
    representative for each multiset. -/
noncomputable def repCount (A : Set ℕ) (k n : ℕ) : ℕ :=
  Set.ncard {l : List ℕ | l.length ≤ k ∧ l.Pairwise (· ≤ ·) ∧
    (∀ x ∈ l, x ∈ A) ∧ l.sum = n}

/--
Erdős Problem #870 [ErNa88]:

For every k ≥ 3, there exists c > 0 (depending only on k) such that for every
additive basis A of order k, if the representation count r(n) ≥ c · log(n) for
all sufficiently large n, then A contains a minimal additive basis of order k.
-/
theorem erdos_problem_870 (k : ℕ) (hk : k ≥ 3) :
    ∃ c : ℝ, c > 0 ∧
      ∀ (A : Set ℕ), IsAdditiveBasis A k →
        (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → (repCount A k n : ℝ) ≥ c * Real.log n) →
        ∃ B : Set ℕ, B ⊆ A ∧ IsMinimalAdditiveBasis B k :=
  sorry

end
