import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

open Classical SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #1034

Let G be a graph on n vertices with > n²/4 many edges. Must there be a
triangle T in G and vertices y₁,...,yₜ, where t > (1/2 - o(1))n, such
that every vertex yᵢ is joined to at least two vertices of T?

A conjecture of Erdős and Faudree [Er93, p.344]; a stronger version of #905.

**Disproved** by Ma and Tang, who construct a graph with n vertices and
> n²/4 edges in which every triangle has at most (2 - √(5/2) + o(1))n
vertices adjacent to at least two of its vertices (2 - √(5/2) ≈ 0.4189).

Tags: graph theory
-/

/-- The number of vertices in a graph adjacent to at least two of three
    given vertices u, v, w. -/
def adjToAtLeastTwoOfTriangle {n : ℕ} (G : SimpleGraph (Fin n))
    (u v w : Fin n) : ℕ :=
  (Finset.univ.filter fun x : Fin n =>
    (G.Adj x u ∧ G.Adj x v) ∨ (G.Adj x v ∧ G.Adj x w) ∨ (G.Adj x u ∧ G.Adj x w)).card

/--
**Erdős Problem #1034** (Disproved) [Er93, p.344]:

For every ε > 0, there exists N₀ such that for all n ≥ N₀, every graph on
n vertices with more than n²/4 edges contains a triangle {u, v, w} such that
more than (1/2 - ε) · n vertices are each adjacent to at least two of u, v, w.

This conjecture was disproved by Ma and Tang.
-/
theorem erdos_problem_1034 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.edgeFinset.card > n ^ 2 / 4 →
      ∃ u v w : Fin n, G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧
        (adjToAtLeastTwoOfTriangle G u v w : ℝ) > (1 / 2 - ε) * (n : ℝ) :=
  sorry

end
