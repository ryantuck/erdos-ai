import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #545

Let G be a graph with m edges and no isolated vertices. Is the Ramsey number R(G)
maximised when G is 'as complete as possible'? That is, if m = C(n,2) + t edges
with 0 ≤ t < n then is R(G) ≤ R(H), where H is the graph formed by connecting a
new vertex to t of the vertices of K_n?

A question of Erdős and Graham [ErGr75, Er84b].
-/

/-- A graph H contains a copy of graph G (as a subgraph) if there is an injective
    function from V(G) to V(H) that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The diagonal Ramsey number R(G) for a graph G on Fin k: the minimum N such that
    every graph H on N vertices contains a copy of G or its complement contains
    a copy of G. -/
noncomputable def ramseyNumber {k : ℕ} (G : SimpleGraph (Fin k)) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    ContainsSubgraphCopy G H ∨ ContainsSubgraphCopy G Hᶜ}

/-- The "as complete as possible" graph with n.choose 2 + t edges on n + 1 vertices.
    The first n vertices form K_n, and the last vertex is adjacent to the
    first t of K_n's vertices. -/
def asCompleteAsPossible (n t : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj u v :=
    u ≠ v ∧ ((u.val < n ∧ v.val < n) ∨
             (u.val = n ∧ v.val < t) ∨
             (v.val = n ∧ u.val < t))
  symm u v := by
    rintro ⟨hne, h | h | h⟩
    · exact ⟨hne.symm, Or.inl ⟨h.2, h.1⟩⟩
    · exact ⟨hne.symm, Or.inr (Or.inr h)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl h)⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/--
Erdős Problem #545 [ErGr75, Er84b]:

Let G be a graph with m edges and no isolated vertices. Is the Ramsey number
R(G) maximised when G is 'as complete as possible'? That is, if
m = n.choose 2 + t edges with 0 ≤ t < n then is R(G) ≤ R(H), where H
is the graph formed by connecting a new vertex to t of the vertices of K_n?
-/
theorem erdos_problem_545 (n t k : ℕ) (ht : t < n)
    (G : SimpleGraph (Fin k))
    (hm : G.edgeSet.ncard = n.choose 2 + t)
    (hiso : ∀ v : Fin k, ∃ w : Fin k, G.Adj v w) :
    ramseyNumber G ≤ ramseyNumber (asCompleteAsPossible n t) :=
  sorry

end
