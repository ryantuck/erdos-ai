import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Real Classical

noncomputable section

/-!
# Erdős Problem #801

If G is a graph on n vertices containing no independent set on > n^{1/2}
vertices then there is a set of ≤ n^{1/2} vertices containing ≫ n^{1/2} log n
edges.

Proved by Alon [Al96b].

https://www.erdosproblems.com/801

Tags: graph theory, ramsey theory
-/

/-- The number of edges in the subgraph of G induced by a subset S of vertices,
    counted as the number of adjacent pairs {u, v} with u, v ∈ S and u < v. -/
noncomputable def Erdos801.inducedEdgeCount {n : ℕ}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/--
Erdős Problem #801 [Er79g]:

If G is a graph on n vertices with no independent set of size > √n,
then there exists a set of ≤ √n vertices containing ≫ √n log n edges.

Formally: there exists a constant C > 0 such that for all sufficiently large n,
for every graph G on n vertices, if G has no independent set of size > ⌊√n⌋,
then there exists a subset S with |S| ≤ ⌊√n⌋ and the number of edges in G[S]
is at least C · √n · log n.

Proved by Alon [Al96b].
-/
theorem erdos_problem_801 :
    ∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ G : SimpleGraph (Fin n),
    (∀ S : Finset (Fin n), Gᶜ.IsClique (S : Set (Fin n)) → S.card ≤ Nat.sqrt n) →
    ∃ S : Finset (Fin n),
      S.card ≤ Nat.sqrt n ∧
      C * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ≤
        (Erdos801.inducedEdgeCount G S : ℝ) :=
  sorry

end
