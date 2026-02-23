import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #800

If G is a graph on n vertices which has no two adjacent vertices of degree ≥ 3 then
R(G) ≪ n, where the implied constant is absolute.

A problem of Burr and Erdős [BuEr75]. Solved in the affirmative by Alon [Al94].
This is a special case of problem #163.

Tags: graph theory, ramsey theory
-/

/-- A graph G on Fin n has a subgraph copy in H if there is an injective function
    that preserves adjacency. -/
def HasSubgraphCopy {n N : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin N)) : Prop :=
  ∃ f : Fin n → Fin N, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The graph Ramsey number R(G): the minimum N such that for every graph H on
    Fin N, either G embeds into H or G embeds into Hᶜ as a subgraph. -/
noncomputable def graphRamseyNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)), HasSubgraphCopy G H ∨ HasSubgraphCopy G Hᶜ}

/--
Erdős Problem #800 (Burr–Erdős [BuEr75]):

If G is a graph on n vertices which has no two adjacent vertices of degree ≥ 3,
then R(G) ≪ n, where the implied constant is absolute.

Formally: there exists an absolute constant C > 0 such that for all n and every
graph G on n vertices where no edge has both endpoints of degree ≥ 3,
the graph Ramsey number R(G) ≤ C · n.

Proved by Alon [Al94].
-/
theorem erdos_problem_800 :
    ∃ C : ℝ, C > 0 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (h : DecidableRel G.Adj),
        haveI := h
        (∀ u v, G.Adj u v → G.degree u < 3 ∨ G.degree v < 3) →
        (graphRamseyNumber G : ℝ) ≤ C * (n : ℝ) := by
  sorry

end
