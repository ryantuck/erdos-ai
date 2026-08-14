import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal

/--
Erdős Problem #1128 (Disproved, $50 prize) [Er81b,p.33]:

A problem of Erdős and Hajnal. Let A, B, C be three sets of cardinality ℵ₁.
Is it true that, in any 2-colouring of A × B × C, there must exist
A₁ ⊂ A, B₁ ⊂ B, C₁ ⊂ C, all of cardinality ℵ₀, such that
A₁ × B₁ × C₁ is monochromatic?

The answer is no. This was disproved by Prikry and Mills in 1978, but this seems
to have been unpublished; the disproof is reported by Todorčević [To94] and
Komjáth [Ko25b]. (erdosproblems.com status banner: "DISPROVED — This has been
solved in the negative." Page last edited 30 December 2025, accessed 2026-02-23.
Tags: set theory, ramsey theory, hypergraphs.)

The theorem below asserts the true (negative) direction directly: there exist
sets of cardinality ℵ₁ and a 2-colouring of their triple product admitting no
monochromatic A₁ × B₁ × C₁ with all three sides of cardinality ℵ₀. Since the
property transports along bijections, a single witnessing triple of types is
equivalent to the failure for every triple of sets of cardinality ℵ₁.

References:

[Er81b] Erdős, P., _My Scottish Book 'Problems'_. The Scottish Book (1981),
27-35. (The problem is stated on p. 33.)

[To94] Todorčević, S. (1994). (Stub: surname from the problem page; year
inferred from the citation key; full bibliographic details not recoverable
offline.)

[Ko25b] Komjáth, P. (2025). (Stub: surname from the problem page; year
inferred from the citation key; full bibliographic details not recoverable
offline.)
-/
theorem erdos_problem_1128 :
    ∃ (α β γ : Type) (_ : #α = aleph 1) (_ : #β = aleph 1) (_ : #γ = aleph 1)
      (f : α × β × γ → Fin 2),
      ∀ (A₁ : Set α) (B₁ : Set β) (C₁ : Set γ),
        #A₁ = aleph 0 → #B₁ = aleph 0 → #C₁ = aleph 0 →
        ¬∃ c : Fin 2, ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ x ∈ C₁, f (a, b, x) = c :=
  sorry
