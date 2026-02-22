import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Erdős Problem #586

Is there a covering system such that no two of the moduli divide each other?

Asked by Schinzel, motivated by a question of Erdős and Selfridge.
The answer is no, as proved by Balister, Bollobás, Morris, Sahasrabudhe,
and Tiba [BBMST22].

A *covering system* is a finite collection of residue classes
`a₁ mod n₁, a₂ mod n₂, ..., aₖ mod nₖ` (with each `nᵢ ≥ 2`)
such that every integer belongs to at least one of these classes.

The theorem states that in any such covering system, there must exist
two distinct indices whose moduli are comparable under divisibility
(i.e., one divides the other).
-/

/-- A covering system: a finite collection of residue classes `aᵢ mod nᵢ` (with `nᵢ ≥ 2`)
    that covers every integer. -/
def IsCoveringSystem (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ) : Prop :=
  (∀ i : Fin k, 2 ≤ n i) ∧
  (∀ z : ℤ, ∃ i : Fin k, (n i : ℤ) ∣ (z - a i))

/-- **Erdős Problem #586** (Schinzel): Every covering system has two moduli where one
    divides the other. Equivalently, there is no covering system with pairwise
    non-divisible moduli. Proved by Balister, Bollobás, Morris, Sahasrabudhe,
    and Tiba [BBMST22]. -/
theorem erdos_problem_586 :
    ∀ (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ),
      IsCoveringSystem k a n →
      ∃ i j : Fin k, i ≠ j ∧ (n i ∣ n j ∨ n j ∣ n i) :=
  sorry
