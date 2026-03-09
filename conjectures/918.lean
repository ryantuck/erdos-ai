import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal SimpleGraph

universe u

/-- A graph is properly colorable with at most κ colors (cardinal-valued).
    That is, there exists a type α with #α ≤ κ and a proper coloring of G
    into α. -/
def SimpleGraph.CardColorable {V : Type u} (G : SimpleGraph V) (κ : Cardinal.{u}) : Prop :=
  ∃ (α : Type u), #α ≤ κ ∧ Nonempty (G.Coloring α)

/--
Erdős Problem #918, Part 1 [ErHa68b][Er69b]:

Is there a graph with ℵ₂ vertices and chromatic number ℵ₂ such that every
subgraph on at most ℵ₁ vertices has chromatic number ≤ ℵ₀?

A question of Erdős and Hajnal, who proved that for every finite k there is
a graph with chromatic number ℵ₁ where each subgraph on fewer than ℵ_k
vertices has chromatic number ≤ ℵ₀.
-/
theorem erdos_problem_918a :
    ∃ (V : Type) (G : SimpleGraph V),
      #V = ℵ_ 2 ∧
      ¬G.CardColorable (ℵ_ 1) ∧
      ∀ (S : Set V), #↥S ≤ ℵ_ 1 → (G.induce S).CardColorable ℵ₀ :=
  sorry

/--
Erdős Problem #918, Part 2 [ErHa68b][Er69b]:

Is there a graph with ℵ_{ω+1} vertices and chromatic number ℵ₁ such that
every subgraph on at most ℵ_ω vertices has chromatic number ≤ ℵ₀?
-/
theorem erdos_problem_918b :
    ∃ (V : Type) (G : SimpleGraph V),
      #V = ℵ_ (Ordinal.omega0 + 1) ∧
      G.CardColorable (ℵ_ 1) ∧
      ¬G.CardColorable ℵ₀ ∧
      ∀ (S : Set V), #↥S ≤ ℵ_ Ordinal.omega0 → (G.induce S).CardColorable ℵ₀ :=
  sorry
