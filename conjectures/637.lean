import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Classical

noncomputable section

/-!
# Erdős Problem #637

If G is a graph on n vertices which contains no complete graph or independent
set on ≫ log n vertices then G contains an induced subgraph on ≫ n vertices
which contains ≫ n^{1/2} distinct degrees.

A problem of Erdős, Faudree, and Sós [Er97d].

This was proved by Bukh and Sudakov [BuSu07].

Jenssen, Keevash, Long, and Yepremyan [JKLY20] proved that there must exist
an induced subgraph which contains ≫ n^{2/3} distinct degrees (with no
restriction on the number of vertices).

Tags: graph theory, ramsey theory
-/

/-- The degree of vertex v in the induced subgraph G[S]. -/
noncomputable def inducedDegree {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  (S.filter fun w => G.Adj v w).card

/-- The number of distinct degrees realized by vertices of S in the induced
    subgraph G[S]. -/
noncomputable def inducedDistinctDegrees {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  (S.image fun v => inducedDegree G S v).card

/--
**Erdős Problem #637** (PROVED) [Er97d]:

For every C > 0, there exist c₁ > 0, c₂ > 0, and N₀ such that for all n ≥ N₀,
if G is a graph on n vertices with clique number at most C · log₂(n) and
independence number at most C · log₂(n), then there exists a subset S of
vertices with |S| ≥ c₁ · n such that the induced subgraph G[S] has at least
c₂ · n^{1/2} distinct degrees.

Proved by Bukh and Sudakov [BuSu07].
-/
theorem erdos_problem_637 :
    ∀ C : ℝ, C > 0 →
    ∃ c₁ : ℝ, c₁ > 0 ∧
    ∃ c₂ : ℝ, c₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
    (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
      (S.card : ℝ) ≤ C * Real.logb 2 (↑n : ℝ)) →
    (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
      (S.card : ℝ) ≤ C * Real.logb 2 (↑n : ℝ)) →
    ∃ S : Finset (Fin n), (S.card : ℝ) ≥ c₁ * (↑n : ℝ) ∧
      (inducedDistinctDegrees G S : ℝ) ≥ c₂ * (↑n : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

end
