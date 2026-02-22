import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #621

Let G be a graph on n vertices, α₁(G) be the maximum number of edges forming
a set that contains at most one edge from every triangle, and τ₁(G) be the
minimum number of edges forming a set that contains at least one edge from
every triangle.

Is it true that α₁(G) + τ₁(G) ≤ n²/4?

A problem of Erdős, Gallai, and Tuza [EGT96], who observe that this is probably
quite difficult since there are different examples where equality holds: the
complete graph, the complete bipartite graph, and the graph obtained from K_{m,m}
by adding one vertex joined to every other.

This was proved by Norin and Sun [NoSu16], who in fact proved the stronger result
that α₁(G) + τ_B(G) ≤ n²/4, where τ_B(G) is the minimum number of edges that
need to be removed to make the graph bipartite.

Tags: graph theory
-/

/-- Create an unordered pair from two vertices, representing an edge. -/
abbrev mkEdge621 {V : Type*} (a b : V) : Sym2 V := Quot.mk _ (a, b)

/-- A set of edges S is triangle-independent in G if S ⊆ E(G) and every
    triangle in G contains at most one edge from S. -/
def IsTriangleIndependent621 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Sym2 (Fin n))) : Prop :=
  S ⊆ G.edgeFinset ∧
  ∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj a c →
    ¬(mkEdge621 a b ∈ S ∧ mkEdge621 b c ∈ S) ∧
    ¬(mkEdge621 a b ∈ S ∧ mkEdge621 a c ∈ S) ∧
    ¬(mkEdge621 b c ∈ S ∧ mkEdge621 a c ∈ S)

/-- A set of edges T is a triangle transversal in G if T ⊆ E(G) and every
    triangle in G contains at least one edge from T. -/
def IsTriangleTransversal621 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Sym2 (Fin n))) : Prop :=
  T ⊆ G.edgeFinset ∧
  ∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj a c →
    mkEdge621 a b ∈ T ∨ mkEdge621 b c ∈ T ∨ mkEdge621 a c ∈ T

/--
**Erdős Problem #621** (Erdős-Gallai-Tuza conjecture) [EGT96][Er99]:

Let G be a graph on n vertices. Define α₁(G) as the maximum number of edges
forming a set that contains at most one edge from every triangle, and τ₁(G) as
the minimum number of edges forming a set that contains at least one edge from
every triangle.

Conjecture: α₁(G) + τ₁(G) ≤ n²/4.

This was proved by Norin and Sun (2016).
-/
theorem erdos_problem_621 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Sym2 (Fin n)))
    (hS : IsTriangleIndependent621 G S)
    (hS_max : ∀ S' : Finset (Sym2 (Fin n)), IsTriangleIndependent621 G S' → S'.card ≤ S.card)
    (T : Finset (Sym2 (Fin n)))
    (hT : IsTriangleTransversal621 G T)
    (hT_min : ∀ T' : Finset (Sym2 (Fin n)), IsTriangleTransversal621 G T' → T.card ≤ T'.card) :
    4 * (S.card + T.card) ≤ n ^ 2 :=
  sorry

end
