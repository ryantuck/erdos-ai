import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #80

Let $c > 0$ and let $f_c(n)$ be the maximal $m$ such that every graph $G$ with
$n$ vertices and at least $cn^2$ edges, where each edge is contained in at least
one triangle, must contain a book of size $m$, that is, an edge shared by at least
$m$ different triangles.

Estimate $f_c(n)$. In particular, is it true that $f_c(n) \gg \log n$?

A problem of Erdős and Rothschild. Alon and Trotter showed that, provided $c < 1/4$,
$f_c(n) \ll_c n^{1/2}$. Szemerédi observed that his regularity lemma implies
$f_c(n) \to \infty$. Fox and Loh proved that $f_c(n) \le n^{O(1/\log\log n)}$ for
all $c < 1/4$, disproving the stronger conjecture $f_c(n) > n^\varepsilon$.

The weaker conjecture $f_c(n) \gg \log n$ remains open.
-/

/-- The number of common neighbors of `u` and `v` in `G`, equivalently the number of
    triangles containing the edge `{u, v}` (i.e., the book size at that edge). -/
def bookSize {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  ((G.neighborFinset u) ∩ (G.neighborFinset v)).card

/-- Every edge of `G` is contained in at least one triangle. -/
def EveryEdgeInTriangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v : V, G.Adj u v → 0 < bookSize G u v

/-- **Erdős Problem #80**: For every $c > 0$, there exists $C > 0$ such that every
    graph on $n$ vertices with at least $cn^2$ edges, where every edge lies in a
    triangle, contains an edge that is in at least $C \log n$ triangles. -/
theorem erdos_problem_80 :
    ∀ c : ℝ, c > 0 →
    ∃ C : ℝ, C > 0 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) ^ 2 →
      EveryEdgeInTriangle G →
      ∃ u v : Fin n, G.Adj u v ∧
        (bookSize G u v : ℝ) ≥ C * Real.log (n : ℝ) := by
  sorry

end
