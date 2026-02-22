import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open SimpleGraph Classical

/-!
# Erdős Problem #600

Let e(n,r) be minimal such that every graph on n vertices with at least e(n,r)
edges, each edge contained in at least one triangle, must have an edge contained
in at least r triangles. Let r ≥ 2. Is it true that

  e(n, r+1) - e(n, r) → ∞

as n → ∞? Is it true that

  e(n, r+1) / e(n, r) → 1

as n → ∞?

Ruzsa and Szemerédi [RuSz78] proved that e(n,r) = o(n²) for any fixed r.

See also problem [80].
-/

/-- The number of triangles containing the edge {u, v} in graph G:
    the count of vertices w ≠ u, w ≠ v with G.Adj u w and G.Adj v w. -/
noncomputable def trianglesThrough {n : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => w ≠ u ∧ w ≠ v ∧ G.Adj u w ∧ G.Adj v w).card

/-- A graph is triangle-covered if every edge is contained in at least one triangle. -/
def IsTriangleCovered {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → 0 < trianglesThrough G u v

/-- e(n, r): the minimal number of edges such that every triangle-covered graph
    on n vertices with at least that many edges has an edge in at least r triangles. -/
noncomputable def erdosE (n r : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n),
    IsTriangleCovered G → G.edgeFinset.card ≥ m →
    ∃ u v : Fin n, G.Adj u v ∧ trianglesThrough G u v ≥ r}

/--
Erdős Problem #600, Part 1 [Er87]:

For any r ≥ 2, e(n, r+1) - e(n, r) → ∞ as n → ∞.
That is, for any bound M, for all sufficiently large n,
  erdosE n (r + 1) ≥ erdosE n r + M.
-/
theorem erdos_problem_600_difference (r : ℕ) (hr : r ≥ 2) :
    ∀ M : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      erdosE n (r + 1) ≥ erdosE n r + M :=
  sorry

/--
Erdős Problem #600, Part 2 [Er87]:

For any r ≥ 2, e(n, r+1) / e(n, r) → 1 as n → ∞.
-/
theorem erdos_problem_600_ratio (r : ℕ) (hr : r ≥ 2) :
    Filter.Tendsto
      (fun n : ℕ => (erdosE n (r + 1) : ℝ) / (erdosE n r : ℝ))
      Filter.atTop (nhds 1) :=
  sorry

end
