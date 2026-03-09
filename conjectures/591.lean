import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

open Ordinal

noncomputable section

/-!
# Erdős Problem #591

Let α = ω^(ω²). Is it true that in any red/blue colouring of the edges of K_α
there is either a red K_α or a blue K₃?

In other words, is it true that α → (α, 3)²?

Specker proved this holds when α = ω² and fails when α = ωⁿ for 3 ≤ n < ω.
Chang proved it holds when α = ω^ω (see problem 590).

This was proved independently by Schipperus and Darby.

Tags: set theory, ramsey theory
-/

/-- The type of ordinals strictly less than α. -/
abbrev OrdinalSet (α : Ordinal) := {a : Ordinal // a < α}

/-- The ordinal partition relation α → (β, k)²:
    For every 2-coloring of ordered pairs from OrdinalSet α, either:
    - there is an order-embedded copy of β whose pairs are all color 0, or
    - there exist k pairwise distinct elements whose pairs are all color 1. -/
def OrdPartition (α β : Ordinal) (k : ℕ) : Prop :=
  ∀ (f : OrdinalSet α → OrdinalSet α → Fin 2),
    (∃ e : OrdinalSet β ↪o OrdinalSet α,
      ∀ i j : OrdinalSet β, i < j → f (e i) (e j) = 0) ∨
    (∃ S : Finset (OrdinalSet α), S.card = k ∧
      ∀ x ∈ S, ∀ y ∈ S, x < y → f x y = 1)

/--
Erdős Problem #591 [Er82e, Er87] [Va99, 7.82]:

Is it true that ω^(ω²) → (ω^(ω²), 3)²?

Equivalently, in any red/blue colouring of the edges of the complete graph on
ω^(ω²) vertices, there is either a red clique of order type ω^(ω²) or a blue
triangle.

This is true, proved independently by Schipperus [Sc10] and Darby.
-/
theorem erdos_problem_591 :
    OrdPartition
      (omega0 ^ (omega0 ^ 2))
      (omega0 ^ (omega0 ^ 2))
      3 :=
  sorry

end
