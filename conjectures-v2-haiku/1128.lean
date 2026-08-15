import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal

/--
Erdős Problem #1128 (Disproved) [Er81b,p.33]:

A problem of Erdős and Hajnal. Let A, B, C be three sets of cardinality ℵ₁.
Is it true that, in any 2-colouring of A × B × C, there must exist
A₁ ⊂ A, B₁ ⊂ B, C₁ ⊂ C, all of cardinality ℵ₀, such that
A₁ × B₁ × C₁ is monochromatic?

The answer is no. This was disproved by Prikry and Mills in 1978
(unpublished), as reported by Todorčević and Komjáth.
-/
theorem erdos_problem_1128 :
    ∃ (α β γ : Type) (_ : #α = aleph 1) (_ : #β = aleph 1) (_ : #γ = aleph 1)
      (f : α × β × γ → Fin 2),
      ∀ (A₁ : Set α) (B₁ : Set β) (C₁ : Set γ),
        #A₁ = aleph 0 → #B₁ = aleph 0 → #C₁ = aleph 0 →
        ¬∃ c : Fin 2, ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ x ∈ C₁, f (a, b, x) = c :=
  sorry
