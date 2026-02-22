import Mathlib.Data.Set.Finite.Basic

noncomputable section

/-!
# Erdős Problem #869

If $A_1, A_2$ are disjoint additive bases of order $2$ (i.e., $A_i + A_i$ contains
all sufficiently large integers) then must $A = A_1 \cup A_2$ contain a minimal
additive basis of order $2$ (one such that deleting any element creates infinitely
many $n \notin A + A$)?

A question of Erdős and Nathanson [ErNa88].

Tags: number theory, additive basis
-/

/-- The sumset `A + A`: the set of all `a + b` with `a, b ∈ A`. -/
def sumset869 (A : Set ℕ) : Set ℕ := {n : ℕ | ∃ a ∈ A, ∃ b ∈ A, n = a + b}

/-- A set `A ⊆ ℕ` is an additive basis of order 2 if every sufficiently large
    natural number can be written as `a + b` with `a, b ∈ A`. -/
def IsAdditiveBasis2_869 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → n ∈ sumset869 A

/-- A set `B ⊆ ℕ` is a minimal additive basis of order 2 if it is an additive
    basis of order 2 and for every element `x ∈ B`, the set of natural numbers
    not in the sumset of `B \ {x}` is infinite. -/
def IsMinimalAdditiveBasis2_869 (B : Set ℕ) : Prop :=
  IsAdditiveBasis2_869 B ∧
    ∀ x ∈ B, Set.Infinite {n : ℕ | n ∉ sumset869 (B \ {x})}

/--
**Erdős Problem #869** [ErNa88]:

If $A_1$ and $A_2$ are disjoint additive bases of order $2$, then
$A_1 \cup A_2$ contains a minimal additive basis of order $2$.
-/
theorem erdos_problem_869
    (A₁ A₂ : Set ℕ)
    (hA₁ : IsAdditiveBasis2_869 A₁)
    (hA₂ : IsAdditiveBasis2_869 A₂)
    (hDisjoint : Disjoint A₁ A₂) :
    ∃ B : Set ℕ, B ⊆ A₁ ∪ A₂ ∧ IsMinimalAdditiveBasis2_869 B :=
  sorry

end
