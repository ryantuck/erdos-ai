import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

open Finset

/--
A covering system is a finite collection of arithmetic progressions {x | x ≡ a (mod n)}
whose union is the set of all integers.
Following Erdős, we require that the moduli are distinct and greater than 1.
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  (∀ s ∈ S, s.2 > 1) ∧ 
  (∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → s₁.2 ≠ s₂.2) ∧
  (∀ x : ℤ, ∃ s ∈ S, Int.ModEq s.2 x s.1)

/--
Erdős' conjecture on covering systems (Problem #2):
The smallest modulus of a covering system can be arbitrarily large.
-/
theorem erdos_problem_2_conjecture :
  ∀ M : ℕ, ∃ S : Finset (ℤ × ℕ), IsCoveringSystem S ∧ ∀ s ∈ S, s.2 ≥ M :=
sorry
