import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finite.Defs

open Finset

/--
A covering system is a finite collection of arithmetic progressions {x | x ≡ a (mod n)}
whose union is the set of all integers.
Following Erdős, we require that the moduli are distinct and greater than 1.
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  (∀ s ∈ S, 1 < s.2) ∧
  (∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → s₁.2 ≠ s₂.2) ∧
  (∀ x : ℤ, ∃ s ∈ S, x ≡ s.1 [ZMOD s.2])

/--
Erdős-Graham conjecture on monochromatic covering systems (Problem #8):
For any finite colouring of the positive integers, there exists a covering system
all of whose moduli are monochromatic.
-/
theorem erdos_problem_8 (α : Type*) [Finite α] (c : ℕ → α) :
  ∃ S : Finset (ℤ × ℕ), IsCoveringSystem S ∧
  ∃ color : α, ∀ s ∈ S, c s.2 = color :=
sorry
