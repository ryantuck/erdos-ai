import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #568

Let G be a graph such that R(G, Tₙ) ≪ n for any tree Tₙ on n vertices
and R(G, Kₙ) ≪ n². Is it true that, for any H with m edges and no
isolated vertices, R(G, H) ≪ m?

In other words, is G Ramsey size linear?

A problem of Erdős, Faudree, Rousseau, and Schelp [EFRS93].
-/

/-- A graph G embeds into a graph H: there is an injective map from
    vertices of G to vertices of H preserving adjacency. -/
def SimpleGraph.Embeds {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The Ramsey number R(G, H): the minimum N such that for any graph F
    on Fin N, either G embeds in F or H embeds in the complement of F. -/
noncomputable def ramseyNum {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : ℕ :=
  sInf {N : ℕ | ∀ (F : SimpleGraph (Fin N)),
    G.Embeds F ∨ H.Embeds Fᶜ}

/-- A graph is connected if any two vertices are related by the reflexive
    transitive closure of adjacency. -/
def SimpleGraph.IsConnectedGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, Relation.ReflTransGen G.Adj u v

/-- A tree is a connected graph on n vertices with exactly n - 1 edges. -/
def SimpleGraph.IsTreeGraph {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.IsConnectedGraph ∧ G.edgeSet.ncard + 1 = Fintype.card V

/--
Erdős Problem #568:

Let G be a graph such that:
(1) R(G, T) = O(n) for every tree T on n vertices, and
(2) R(G, Kₙ) = O(n²).

Is it true that for any graph H with m edges and no isolated vertices,
R(G, H) = O(m)?

In other words, is G Ramsey size linear?
-/
theorem erdos_problem_568 {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (h_tree : ∃ C₁ : ℕ, ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
      T.IsTreeGraph → ramseyNum G T ≤ C₁ * n)
    (h_clique : ∃ C₂ : ℕ, ∀ (n : ℕ),
      ramseyNum G (⊤ : SimpleGraph (Fin n)) ≤ C₂ * n ^ 2) :
    ∃ C : ℕ, ∀ (k : ℕ) (H : SimpleGraph (Fin k)),
      (∀ v : Fin k, ∃ w, H.Adj v w) →
      ramseyNum G H ≤ C * H.edgeSet.ncard :=
  sorry

end
