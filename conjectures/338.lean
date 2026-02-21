import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Set BigOperators Classical

/-- The set of all sums of exactly `k` elements from `A` (with repetition allowed). -/
def exactSumset338 (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (f : Fin k → ℕ), (∀ i, f i ∈ A) ∧ n = ∑ i, f i}

/-- `A ⊆ ℕ` is an additive basis of order `h` if every sufficiently large
    natural number is the sum of at most `h` elements from `A` (with repetition). -/
def IsAdditiveBasis338 (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ k ≤ h, n ∈ exactSumset338 A k

/-- `n` is the sum of at most `t` distinct elements from `A`:
    there exists a finite subset `s ⊆ A` with `s.card ≤ t` and `s.sum id = n`. -/
def IsDistinctSum338 (A : Set ℕ) (t : ℕ) (n : ℕ) : Prop :=
  ∃ (s : Finset ℕ), ↑s ⊆ A ∧ s.card ≤ t ∧ s.sum id = n

/-- `A` has restricted order at most `t` if every sufficiently large natural number
    is the sum of at most `t` distinct elements from `A`. -/
def HasRestrictedOrderAtMost338 (A : Set ℕ) (t : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, IsDistinctSum338 A t n

/-- `A` has a restricted order (i.e., some finite restricted order exists). -/
def HasRestrictedOrder338 (A : Set ℕ) : Prop :=
  ∃ t : ℕ, HasRestrictedOrderAtMost338 A t

/--
Erdős Problem #338 [ErGr80, ErGr80b]:

The restricted order of a basis A ⊆ ℕ is the least integer t (if it exists) such that
every sufficiently large integer is the sum of at most t distinct elements from A.

Bateman observed that for h ≥ 3, the basis A = {1} ∪ {x > 0 : h ∣ x} has order h
but no restricted order. Kelly showed that any basis of order 2 has restricted order
at most 4. Hennecart constructed a basis of order 2 with restricted order exactly 4.

The problem asks: what are necessary and sufficient conditions for the restricted order
to exist, and can it be bounded in terms of the order of the basis?

A specific sub-conjecture asks: if A \ F is a basis of the same order h for every
finite set F ⊆ ℕ, must A have a restricted order? We formalize this sub-conjecture.
-/
theorem erdos_problem_338 :
    ∀ (A : Set ℕ) (h : ℕ),
      (∀ (F : Finset ℕ), IsAdditiveBasis338 (A \ ↑F) h) →
      HasRestrictedOrder338 A :=
  sorry
