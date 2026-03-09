import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Filter Finset Set Classical

noncomputable section

/--
A set A ⊆ ℕ is an additive basis of order h if every sufficiently large
natural number can be represented as a sum of at most h elements of A
(with repetition allowed).
-/
def IsAdditiveBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ m : ℕ, N₀ ≤ m →
    ∃ (k : ℕ) (f : Fin k → ℕ), k ≤ h ∧ (∀ i, f i ∈ A) ∧ ∑ i, f i = m

/--
A set A is a minimal additive basis of order h if it is a basis of order h,
but for every element n ∈ A, the set A \ {n} is not a basis of any order.
-/
def IsMinimalAdditiveBasis (A : Set ℕ) (h : ℕ) : Prop :=
  IsAdditiveBasis A h ∧
    ∀ n ∈ A, ∀ h' : ℕ, ¬IsAdditiveBasis (A \ {n}) h'

/--
The upper density of a set A ⊆ ℕ is positive.
-/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      δ ≤ ({n ∈ Finset.Icc 1 N | n ∈ A}).card / (N : ℝ)

/--
The set of natural numbers that cannot be represented as a sum of at most h
elements of A without using the element n.
-/
def UnrepresentableWithout (A : Set ℕ) (h : ℕ) (n : ℕ) : Set ℕ :=
  {m : ℕ | ¬∃ (k : ℕ) (f : Fin k → ℕ), k ≤ h ∧ (∀ i, f i ∈ A \ {n}) ∧ ∑ i, f i = m}

/--
Erdős Problem #330 [ErGr80, p.50]:

Does there exist a minimal basis with positive density, say A ⊂ ℕ, such that
for any n ∈ A the (upper) density of integers which cannot be represented
without using n is positive?

Asked by Erdős and Nathanson.
-/
theorem erdos_problem_330 :
    ∃ (A : Set ℕ) (h : ℕ),
      IsMinimalAdditiveBasis A h ∧
      HasPositiveUpperDensity A ∧
      ∀ n ∈ A, HasPositiveUpperDensity (UnrepresentableWithout A h n) :=
  sorry
