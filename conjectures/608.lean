import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

noncomputable section

open SimpleGraph Classical

/-!
# Erdős Problem #608

Let G be a graph with n vertices and > n²/4 edges. Are there at least (2/9)n²
edges of G which are contained in a C₅?

This was disproved. Füredi and Maleki constructed graphs with > n²/4 edges
where at most c·n² + O(n) edges are in a C₅, with c = (2 + √2)/16 ≈ 0.2134.
Grzesik, Hu, and Volec [GHV19] proved this is optimal: any graph with > n²/4
edges contains at least (c - o(1))·n² edges in a C₅.

Tags: graph theory
-/

/-- The number of edges of G contained in some 5-cycle. An edge {u, v} is
    in a C₅ if there exist vertices w₁, w₂, w₃ (all five pairwise distinct)
    such that u-w₁-w₂-w₃-v-u is a 5-cycle in G. Edges are counted as
    ordered pairs (u, v) with u < v to avoid double-counting. -/
noncomputable def numEdgesInC5 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ G.Adj p.1 p.2 ∧
    ∃ w₁ w₂ w₃ : Fin n,
      ({p.1, p.2, w₁, w₂, w₃} : Finset (Fin n)).card = 5 ∧
      G.Adj p.1 w₁ ∧ G.Adj w₁ w₂ ∧ G.Adj w₂ w₃ ∧ G.Adj w₃ p.2).card

/--
**Erdős Problem #608** (Disproved) [EFR92, Er97d]:

If G is a graph on n vertices with more than n²/4 edges, then at least
(2/9)·n² edges of G are contained in a C₅.

This is false. The correct threshold is c = (2+√2)/16 ≈ 0.2134, proved
optimal by Grzesik, Hu, and Volec [GHV19].
-/
theorem erdos_problem_608 :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (G.edgeFinset.card : ℝ) > (n : ℝ) ^ 2 / 4 →
      (numEdgesInC5 G : ℝ) ≥ 2 / 9 * (n : ℝ) ^ 2 :=
  sorry

end
