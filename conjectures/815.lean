import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #815

Let $k \geq 3$ and $n$ be sufficiently large. Is it true that if $G$ is a graph
with $n$ vertices and $2n - 2$ edges such that every proper induced subgraph has
minimum degree $\leq 2$ then $G$ must contain a copy of $C_k$?

Such graphs are called *degree 3 critical*. This conjecture was **disproved** by
Narins, Pokrovskiy, and Szabó [NPS17], who proved that there exist arbitrarily
large such graphs with no cycle of length $23$.

It remains open whether the answer is affirmative when restricted to even $k$.

Tags: graph theory
-/

/-- A graph on `Fin n` is *degree 3 critical* if it has `2n - 2` edges and every
    proper induced subgraph has a vertex of degree at most 2. -/
def IsDegree3Critical {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.edgeSet.ncard = 2 * n - 2 ∧
  ∀ S : Finset (Fin n), S.Nonempty → S ⊂ Finset.univ →
    ∃ v ∈ S, ((↑S : Set (Fin n)) ∩ G.neighborSet v).ncard ≤ 2

/--
**Erdős Problem #815** (disproved by Narins–Pokrovskiy–Szabó [NPS17]):

There exist arbitrarily large degree 3 critical graphs containing no cycle
of length 23.
-/
theorem erdos_815 :
    ∀ N : ℕ, ∃ (n : ℕ), n ≥ N ∧ ∃ (G : SimpleGraph (Fin n)),
      IsDegree3Critical G ∧
      ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → p.length ≠ 23 :=
  sorry

end
