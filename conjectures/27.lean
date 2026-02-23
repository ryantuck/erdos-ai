import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

open Finset

open scoped Classical

/-
Erdős Problem #27 (Disproved).

An ε-almost covering system is a set of congruences aᵢ (mod nᵢ) for distinct
moduli n₁ < ⋯ < nₖ such that the natural density of integers satisfying none
of them is at most ε.

Erdős asked: is there a constant C > 1 such that for every ε > 0 and N ≥ 1,
there is an ε-almost covering system with N ≤ n₁ < ⋯ < nₖ ≤ CN?

This was disproved by Filaseta, Ford, Konyagin, Pomerance, and Yu (2007).
We formalize the negation (the proved result).
-/

/-- A congruence system has distinct moduli if no two pairs share the same modulus. -/
def Erdos27.hasDistinctModuli (S : Finset (ℤ × ℕ)) : Prop :=
  S.card = (S.image Prod.snd).card

/-- The LCM of all moduli in a congruence system. -/
noncomputable def Erdos27.systemLcm (S : Finset (ℤ × ℕ)) : ℕ :=
  (S.image Prod.snd).lcm id

/-- The density of uncovered integers for a congruence system,
    measured as the proportion of integers in {0, …, L-1} not covered
    by any congruence, where L = lcm of all moduli. -/
noncomputable def Erdos27.uncoveredDensity (S : Finset (ℤ × ℕ)) : ℝ :=
  let L := Erdos27.systemLcm S
  ((Finset.range L).filter (fun x =>
    ∀ p ∈ S, ¬((↑p.2 : ℤ) ∣ (↑x - p.1)))).card / (L : ℝ)

theorem erdos_problem_27 :
    ¬ ∃ C : ℝ, C > 1 ∧
      ∀ ε : ℝ, ε > 0 →
      ∀ N : ℕ, N ≥ 1 →
      ∃ S : Finset (ℤ × ℕ),
        Erdos27.hasDistinctModuli S ∧
        S.Nonempty ∧
        (∀ p ∈ S, p.2 ≥ 2) ∧
        (∀ p ∈ S, N ≤ p.2 ∧ (p.2 : ℝ) ≤ C * N) ∧
        Erdos27.uncoveredDensity S ≤ ε :=
  sorry
