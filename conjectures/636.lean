import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #636

Suppose G is a graph on n vertices which contains no complete graph or independent
set on ≫ log n many vertices. Must G contain ≫ n^{5/2} induced subgraphs which
pairwise differ in either the number of vertices or the number of edges?

A problem of Erdős, Faudree, and Sós [Er93, p.346], who proved there exist
≫ n^{3/2} many such subgraphs, and note that n^{5/2} would be best possible.

This was proved by Kwan and Sudakov [KwSu21].

Tags: graph theory, ramsey theory
-/

/-- The set of distinct (vertex count, edge count) signatures realized by induced
    subgraphs of a graph G on Fin n. For each subset S of vertices, we record
    (|S|, |E(G[S])|) where G[S] is the induced subgraph on S. -/
noncomputable def inducedSubgraphSignatures {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset (ℕ × ℕ) :=
  Finset.univ.image fun S : Finset (Fin n) =>
    (S.card, (G.induce (↑S : Set (Fin n))).edgeSet.ncard)

/--
**Erdős Problem #636** (PROVED) [Er93, p.346][Er97d]:

For every C > 0, there exist c > 0 and N₀ such that for all n ≥ N₀, if G is a
graph on n vertices with clique number at most C · log₂(n) and independence number
at most C · log₂(n), then G has at least c · n^{5/2} distinct induced subgraph
signatures (pairs (vertex count, edge count) among all induced subgraphs of G).

Proved by Kwan and Sudakov [KwSu21].
-/
theorem erdos_problem_636 :
    ∀ C : ℝ, C > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
    (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
      (S.card : ℝ) ≤ C * Real.logb 2 (↑n : ℝ)) →
    (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
      (S.card : ℝ) ≤ C * Real.logb 2 (↑n : ℝ)) →
    ((inducedSubgraphSignatures G).card : ℝ) ≥ c * (↑n : ℝ) ^ ((5 : ℝ) / 2) :=
  sorry

end
