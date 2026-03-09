import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal SimpleGraph

universe u

/-- A graph is properly colorable with at most κ colors (cardinal-valued). -/
def SimpleGraph.CardColorable1176 {V : Type u} (G : SimpleGraph V) (κ : Cardinal.{u}) : Prop :=
  ∃ (α : Type u), #α ≤ κ ∧ Nonempty (G.Coloring α)

/--
Erdős Problem #1176 [Va99,7.93]:

Let G be a graph with chromatic number ℵ₁. Is it true that there is a
colouring of the edges with ℵ₁ many colours such that, in any countable
colouring of the vertices, there exists a vertex colour containing all edge
colours?

A problem of Erdős, Galvin, and Hajnal. The consistency of this was proved
by Hajnal and Komjáth.

Here "a vertex colour containing all edge colours" means: there is a vertex
color class (the set of vertices assigned the same color) such that every edge
color appears on at least one edge whose both endpoints lie in that class.

https://www.erdosproblems.com/1176
Tags: set theory, ramsey theory
-/
theorem erdos_problem_1176 :
    ∀ (V : Type) (G : SimpleGraph V),
      ¬G.CardColorable1176 ℵ₀ →
      ∃ (EC : Type) (_ : #EC = ℵ₁)
        (edgeColor : G.edgeSet → EC),
        ∀ (VC : Type) (_ : Countable VC)
          (vertexColor : V → VC),
          ∃ (b : VC),
            ∀ (ec : EC), ∃ (e : G.edgeSet),
              edgeColor e = ec ∧
              ∀ v ∈ (e.val : Sym2 V), vertexColor v = b :=
  sorry
