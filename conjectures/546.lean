import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #546

Let G be a graph with no isolated vertices and m edges. Is it true that
R(G) ≤ 2^{O(m^{1/2})}?

This is true, and was proved by Sudakov [Su11]. The analogous question for
≥ 3 colours is still open. A more precise question is [545].
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

/--
Erdős Problem #546 [Er84b,p.10]:

Let G be a graph with no isolated vertices and m edges. Is it true that
R(G) ≤ 2^{O(m^{1/2})}?

Formally: there exists a constant C > 0 such that for every graph G on k
vertices with no isolated vertices, R(G) ≤ 2^(C · √m) where m is the
number of edges.
-/
theorem erdos_problem_546 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (k : ℕ) (G : SimpleGraph (Fin k)),
      (∀ v : Fin k, ∃ w : Fin k, G.Adj v w) →
      (ramseyNumber G : ℝ) ≤ (2 : ℝ) ^ (C * Real.sqrt (G.edgeSet.ncard : ℝ)) :=
  sorry

end
