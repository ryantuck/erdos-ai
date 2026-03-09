import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Order.RelClasses

open Ordinal

noncomputable section

/-!
# Erdős Problem #590

Let α be the infinite ordinal ω^ω. Is it true that in any red/blue colouring
of the edges of K_α there is either a red K_α or a blue K_3?

This is the ordinal partition relation ω^ω → (ω^ω, 3)².

A problem of Erdős and Rado [ErRa56]. This is true, and was proved by
Chang [Ch72]. Milner modified Chang's proof to show it remains true if K_3
is replaced by K_m for any finite m.

https://www.erdosproblems.com/590
Tags: set theory, ramsey theory
-/

/--
Erdős Problem #590 [ErRa56, Er82e]:

The ordinal partition relation ω^ω → (ω^ω, 3)² holds: for any well-ordered
set V of order type ω^ω and any 2-coloring of the edges of the complete graph
on V, either there is a subset of order type ω^ω whose edges are all red, or
there are 3 elements whose edges are all blue.
-/
theorem erdos_problem_590 :
    ∀ (V : Type) [LinearOrder V] [IsWellOrder V (· < ·)],
      Ordinal.type ((· < ·) : V → V → Prop) = omega ^ omega →
      ∀ f : V → V → Bool,
        (∀ x y, f x y = f y x) →
        (∃ (S : Set V),
          Ordinal.type (Subrel (· < ·) S) = omega ^ omega ∧
          ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x y = true) ∨
        (∃ a b c : V, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
          f a b = false ∧ f a c = false ∧ f b c = false) :=
  sorry

end
