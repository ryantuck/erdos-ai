import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Finset Real Classical

noncomputable section

/--
The degree of vertex `v` in the subgraph of `G` induced by vertex set `S`:
the number of vertices in `S` adjacent to `v` in `G`.
-/
def inducedDegree {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  (S.filter (G.Adj v)).card

/--
Erdős Problem #82 [Er93, Er95, Er97d]:

Let F(n) be maximal such that every graph on n vertices contains a regular
induced subgraph on at least F(n) vertices. Prove that F(n)/log n → ∞.

Conjectured by Erdős, Fajtlowicz, and Staton. Ramsey's theorem implies that
F(n) ≫ log n. Bollobás observed that F(n) ≪ n^{1/2+o(1)}. Alon, Krivelevich,
and Sudakov (2007) improved the upper bound to n^{1/2}(log n)^{O(1)}.

The statement below is equivalent to F(n)/log n → ∞: for every constant C > 0,
all sufficiently large graphs on n vertices contain a regular induced subgraph
on at least C · log n vertices.
-/
theorem erdos_problem_82 :
    ∀ C : ℝ, 0 < C →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ G : SimpleGraph (Fin n),
          ∃ S : Finset (Fin n),
            (S.card : ℝ) ≥ C * Real.log n ∧
            ∃ d : ℕ, ∀ v ∈ S, inducedDegree G S v = d :=
  sorry

end
