import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Hom.Basic

open Cardinal SimpleGraph Ordinal

noncomputable section

/-!
# Erdős Problem #601

For which limit ordinals α is it true that if G is a graph with vertex set α
then G must have either an infinite path or an independent set on a set of
vertices with order type α?

A problem of Erdős, Hajnal, and Milner, who proved this is true for
α < ω₁^(ω+2). Erdős offered $250 for showing what happens when
α = ω₁^(ω+2) and $500 for settling the general case.
Larson proved this is true for all α < 2^ℵ₀ assuming Martin's axiom.

Tags: graph theory, set theory
-/

/-- The type of ordinals strictly less than α. -/
abbrev OrdinalSet (α : Ordinal) := {a : Ordinal // a < α}

/-- A graph has an infinite path: an injective sequence of vertices
    such that consecutive vertices are adjacent. -/
def SimpleGraph.HasInfinitePath {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : ℕ → V, Function.Injective f ∧ ∀ n : ℕ, G.Adj (f n) (f (n + 1))

/-- A graph on OrdinalSet α has an independent set of order type α:
    there is an order embedding from OrdinalSet α into itself whose
    image is an independent set. -/
def SimpleGraph.HasIndepSetOfOrderType {α : Ordinal}
    (G : SimpleGraph (OrdinalSet α)) : Prop :=
  ∃ e : OrdinalSet α ↪o OrdinalSet α,
    ∀ i j : OrdinalSet α, i ≠ j → ¬G.Adj (e i) (e j)

/-- The Erdős-Hajnal-Milner property for an ordinal α:
    every graph on vertex set α has either an infinite path or
    an independent set of order type α. -/
def EHMProperty (α : Ordinal) : Prop :=
  ∀ G : SimpleGraph (OrdinalSet α),
    G.HasInfinitePath ∨ G.HasIndepSetOfOrderType

/--
Erdős Problem #601 [EHM70] [Er81] [Er82e] [Er87]:

Every limit ordinal has the Erdős-Hajnal-Milner property: if G is a graph
with vertex set α (a limit ordinal), then G must have either an infinite path
or an independent set of vertices with order type α.

Known results:
- True for α < ω₁^(ω+2) (Erdős-Hajnal-Milner, 1970)
- True for all α < 2^ℵ₀ assuming Martin's axiom (Larson, 1990)
-/
theorem erdos_problem_601 (α : Ordinal) (hα : Order.IsSuccLimit α) :
    EHMProperty α :=
  sorry

end
