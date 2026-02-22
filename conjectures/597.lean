import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Hom.Basic

open Cardinal SimpleGraph

noncomputable section

/-!
# Erdős Problem #597

Let G be a graph on at most ℵ₁ vertices which contains no K₄ and no K_{ℵ₀,ℵ₀}
(the complete bipartite graph with ℵ₀ vertices in each class). Is it true that
  ω₁² → (ω₁·ω, G)²?

Tags: graph theory, ramsey theory, set theory
-/

/-- The type of ordinals strictly less than α. -/
abbrev OrdinalSet (α : Ordinal) := {a : Ordinal // a < α}

/-- A graph G contains a complete bipartite subgraph K_{κ,κ} if there exist
    disjoint vertex sets A and B, each of cardinality at least κ,
    such that every vertex in A is adjacent to every vertex in B. -/
def SimpleGraph.ContainsBiclique {V : Type*} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ (A B : Set V), Disjoint A B ∧ #A ≥ κ ∧ #B ≥ κ ∧
    ∀ a ∈ A, ∀ b ∈ B, G.Adj a b

/-- The ordinal-graph partition relation α → (β, G)²:
    Every 2-coloring of ordered pairs from OrdinalSet α yields either:
    - an order-embedded copy of β whose pairs are all colored 0, or
    - a copy of G in the color-1 graph (an injective map preserving edges).

    Here a "copy of β" is given by an order embedding e : OrdinalSet β ↪o OrdinalSet α,
    and monochromaticity means f (e i) (e j) = 0 for all i < j. A "copy of G"
    is an injective map g : V → OrdinalSet α such that every edge of G maps to
    a pair colored 1. -/
def OrdGraphPartition (α β : Ordinal) {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (f : OrdinalSet α → OrdinalSet α → Fin 2),
    (∃ e : OrdinalSet β ↪o OrdinalSet α,
      ∀ i j : OrdinalSet β, i < j → f (e i) (e j) = 0) ∨
    (∃ g : V → OrdinalSet α, Function.Injective g ∧
      ∀ u v : V, G.Adj u v → g u < g v → f (g u) (g v) = 1)

/--
Erdős Problem #597 [Er87] [Va99, 7.84]:

If G is a graph on at most ℵ₁ vertices containing no K₄ and no K_{ℵ₀,ℵ₀},
then ω₁² → (ω₁·ω, G)².

Erdős and Hajnal proved that ω₁² → (ω₁·ω, 3)². Erdős originally asked this
with just the assumption that G is K₄-free, but Baumgartner proved that
ω₁² ↛ (ω₁·ω, K_{ℵ₀,ℵ₀})².
-/
theorem erdos_problem_597 {V : Type*} (G : SimpleGraph V)
    (hcard : #V ≤ aleph 1)
    (hK4 : G.CliqueFree 4)
    (hbip : ¬G.ContainsBiclique (aleph 0)) :
    OrdGraphPartition
      ((aleph 1).ord ^ 2)
      ((aleph 1).ord * (aleph 0).ord)
      G :=
  sorry

end
