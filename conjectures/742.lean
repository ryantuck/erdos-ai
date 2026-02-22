import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Classical SimpleGraph

noncomputable section

/-!
# Erdős Problem #742

Let $G$ be a graph on $n$ vertices with diameter $2$, such that deleting any
edge increases the diameter of $G$. Is it true that $G$ has at most $n^2/4$ edges?

A conjecture of Murty and Plesnik (see [CaHa79]), also attributed to Ore.
The complete bipartite graph shows that this would be best possible.

This is true (for sufficiently large $n$) and was proved by Füredi [Fu92].

https://www.erdosproblems.com/742

Tags: graph theory
-/

/--
**Erdős Problem #742** [Er81]:

Let G be a graph on n vertices with diameter 2, such that deleting any edge
increases the diameter (either by disconnecting the graph or increasing it
beyond 2). Then G has at most n²/4 edges.
-/
theorem erdos_problem_742 (n : ℕ) (G : SimpleGraph (Fin n))
    (hconn : G.Connected)
    (hdiam : G.diam = 2)
    (hcrit : ∀ v w : Fin n, G.Adj v w →
      ¬(G.deleteEdges {Sym2.mk (v, w)}).Connected ∨
      2 < (G.deleteEdges {Sym2.mk (v, w)}).diam) :
    G.edgeFinset.card ≤ n ^ 2 / 4 :=
  sorry

end
