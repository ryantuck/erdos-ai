import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal SimpleGraph

noncomputable section

namespace Erdos1175

/-!
# Erdős Problem #1175

Let κ be an uncountable cardinal. Must there exist a cardinal λ such that
every graph with chromatic number λ contains a triangle-free subgraph
with chromatic number κ?

Shelah proved that a negative answer is consistent if κ = λ = ℵ₁.

Tags: set theory, chromatic number
-/

/-- The graph G has cardinal chromatic number equal to κ if κ is the minimum
    cardinality of a color set admitting a proper coloring of G:
    - there exists a proper coloring with a color set of cardinality ≤ κ, and
    - every proper coloring uses a color set of cardinality ≥ κ.
    Here G.Coloring α is a graph homomorphism from G to the complete graph on α,
    i.e., a function assigning colors in α to vertices such that adjacent
    vertices receive distinct colors. -/
def HasChromaticNumber {V : Type} (G : SimpleGraph V) (κ : Cardinal.{0}) : Prop :=
  (∃ (α : Type), Cardinal.mk α ≤ κ ∧ Nonempty (G.Coloring α)) ∧
  ∀ (α : Type), Nonempty (G.Coloring α) → κ ≤ Cardinal.mk α

/--
Erdős Problem #1175 [Va99, 7.92]:

Let κ be an uncountable cardinal. Must there exist a cardinal λ such that
every graph with chromatic number λ contains a triangle-free subgraph
with chromatic number κ?

Here HasChromaticNumber G κ means κ is the minimum cardinality of a color set
admitting a proper coloring of G. Triangle-free means G.CliqueFree 3 (no
3-clique, i.e., no triangle). The subgraph relation H ≤ G holds when every
edge of H is also an edge of G.

Shelah proved that a negative answer is consistent if κ = λ = ℵ₁.
-/
theorem erdos_problem_1175 :
    ∀ κ : Cardinal.{0}, aleph 1 ≤ κ →
    ∃ mu : Cardinal.{0},
      ∀ (V : Type) (G : SimpleGraph V), HasChromaticNumber G mu →
        ∃ H : SimpleGraph V, H ≤ G ∧ H.CliqueFree 3 ∧ HasChromaticNumber H κ :=
  sorry

end Erdos1175

end
