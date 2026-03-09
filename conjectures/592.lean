import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Cardinal.Ordinal

open Ordinal Cardinal

noncomputable section

/-!
# Erdős Problem #592

Determine which countable ordinals β have the property that, if α = ω^β, then
in any red/blue colouring of the edges of K_α there is either a red K_α or a
blue K₃. Such α (those with α → (α, 3)²) are called **partition ordinals**.

Specker proved this holds for β = 2 and not for 3 ≤ β < ω. Chang proved it
holds for β = ω. Galvin and Larson showed that if β ≥ 3 has this property then
β must be additively indecomposable (i.e., β = ω^γ for some γ). They
conjectured that every β ≥ 3 of this form has this property. Schipperus proved
this holds if β = ω^γ where γ is a sum of one or two indecomposable ordinals,
and fails if γ is a sum of four or more. The remaining open case is when γ is
a sum of three indecomposable ordinals.

https://www.erdosproblems.com/592
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

/-- An ordinal β is a **partition ordinal** if ω^β → (ω^β, 3)². -/
def IsPartitionOrdinal (β : Ordinal) : Prop :=
  OrdPartition (omega0 ^ β) (omega0 ^ β) 3

/--
Erdős Problem #592 [Er82e, Er87] [Va99, 7.82]:

Determine which countable ordinals β have the property that ω^β → (ω^β, 3)².

By the results of Galvin and Larson, a necessary condition for β ≥ 3 is that
β be additively indecomposable. The conjecture (due to Galvin and Larson) is
that for β ≥ 3, β is a partition ordinal if and only if β = ω^γ for some
countable ordinal γ.
-/
theorem erdos_problem_592 :
    ∀ β : Ordinal, β.card ≤ ℵ₀ → β ≥ 3 →
      (IsPartitionOrdinal β ↔ ∃ γ : Ordinal, β = omega0 ^ γ) :=
  sorry

end
