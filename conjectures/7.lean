import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Ring.Parity

open Finset

/--
A covering system is a finite collection of arithmetic progressions {x | x ≡ a (mod n)}
whose union is the set of all integers.
We require that the moduli are distinct and greater than 1.
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  (∀ s ∈ S, 1 < s.2) ∧
  (∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → s₁.2 ≠ s₂.2) ∧
  (∀ x : ℤ, ∃ s ∈ S, x ≡ s.1 [ZMOD s.2])

/--
Erdős's conjecture on odd covering systems (Problem #7):
There exists a covering system all of whose moduli are odd.
-/
theorem erdos_problem_7 :
  ∃ S : Finset (ℤ × ℕ), IsCoveringSystem S ∧ ∀ s ∈ S, Odd s.2 :=
sorry
