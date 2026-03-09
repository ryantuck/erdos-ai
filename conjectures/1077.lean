import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Prod

open SimpleGraph Finset Classical Real

noncomputable section

/--
The degree of vertex `v` in the subgraph of `G` induced by vertex set `S`:
the number of vertices in `S` adjacent to `v` in `G`.
-/
def inducedDegree {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  (S.filter (G.Adj v)).card

/--
The number of edges in the subgraph of `G` induced by `S`, computed as
half the number of ordered adjacent pairs in `S × S`.
-/
def inducedEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card / 2

/--
A subgraph induced by `S` is `D`-balanced if for every pair of vertices in `S`,
the induced degree of one is at most `D` times the induced degree of the other.
Equivalently, the maximum degree is at most `D` times the minimum degree.
-/
def isDBalanced {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (D : ℕ) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, inducedDegree G S u ≤ D * inducedDegree G S v

/--
Erdős Problem #1077 [ErSi70,p.388] (DISPROVED):

We call a graph D-balanced (or D-almost-regular) if the maximum degree is at
most D times the minimum degree.

Let ε, α > 0 and D and n be sufficiently large. If G is a graph on n vertices
with at least n^{1+α} edges, then must G contain a D-balanced subgraph on
m > n^{1-α} vertices with at least ε·m^{1+α} edges?

This was disproved: JunGao showed the correct threshold is ≈ n^α vertices
(not n^{1-α}), and Jiang–Longbrake proved the matching lower bound with a
6-balanced subgraph.
-/
theorem erdos_problem_1077 :
    ∀ ε : ℝ, 0 < ε →
    ∀ α : ℝ, 0 < α →
      ∃ D₀ N₀ : ℕ, ∀ D : ℕ, D ≥ D₀ → ∀ n : ℕ, n ≥ N₀ →
        ∀ G : SimpleGraph (Fin n),
          (inducedEdgeCount G Finset.univ : ℝ) ≥ (n : ℝ) ^ (1 + α) →
          ∃ S : Finset (Fin n),
            isDBalanced G S D ∧
            (S.card : ℝ) > (n : ℝ) ^ (1 - α) ∧
            (inducedEdgeCount G S : ℝ) ≥ ε * (S.card : ℝ) ^ (1 + α) :=
  sorry

end
