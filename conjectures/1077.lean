import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #1077

We call a graph D-balanced (or D-almost-regular) if the maximum degree is at
most D times the minimum degree.

Let ε, α > 0 and D and n be sufficiently large. If G is a graph on n vertices
with at least n^{1+α} edges, then must G contain a D-balanced subgraph on
m > n^{1-α} vertices with at least εm^{1+α} edges?

A question of Erdős and Simonovits [ErSi70,p.388]. This has been DISPROVED.
The correct bound on vertex count is m ≍ n^α (not n^{1-α}), as shown by
Jiang and Longbrake [JiLo25].

See also problem #803.
-/

/-- A graph is D-balanced if for all vertices u, v, the degree of u is at most
    D times the degree of v (measured via Set.ncard of neighbor sets).
    Equivalently, the maximum degree is at most D times the minimum degree. -/
def SimpleGraph.IsBalanced {V : Type*} (G : SimpleGraph V) (D : ℕ) : Prop :=
  ∀ u v : V, (G.neighborSet u).ncard ≤ D * (G.neighborSet v).ncard

/--
Erdős Problem #1077 [ErSi70,p.388] (DISPROVED):

The original conjecture is false: it is not the case that for all ε, α > 0,
for sufficiently large D and n, every graph on n vertices with at least n^{1+α}
edges contains a D-balanced subgraph on m > n^{1-α} vertices with at least
εm^{1+α} edges.
-/
theorem erdos_problem_1077 :
    ¬ (∀ ε : ℝ, 0 < ε → ε < 1 →
       ∀ α : ℝ, 0 < α → α < 1 →
       ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
       ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
       ∀ G : SimpleGraph (Fin n),
       (G.edgeSet.ncard : ℝ) ≥ (n : ℝ) ^ (1 + α) →
       ∃ H : G.Subgraph,
         H.coe.IsBalanced D ∧
         (H.verts.ncard : ℝ) > (n : ℝ) ^ (1 - α) ∧
         (H.edgeSet.ncard : ℝ) ≥ ε * (H.verts.ncard : ℝ) ^ (1 + α)) :=
  sorry

end
