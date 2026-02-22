import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #922

Let k ≥ 0. Let G be a graph such that every subgraph H contains an independent
set of size ≥ (n - k) / 2, where n is the number of vertices of H. Must G have
chromatic number at most k + 2?

A question of Erdős and Hajnal [ErHa67b]. This is true, and was proved by
Folkman [Fo70b].
-/

/--
Erdős Problem #922 [ErHa67b]:

If every induced subgraph of G on n vertices has an independent set of
size at least (n - k) / 2, then G is (k + 2)-colorable.

The condition `2 * T.card + k ≥ S.card` encodes `T.card ≥ (S.card - k) / 2`.
-/
theorem erdos_problem_922 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ)
    (h : ∀ S : Finset V, ∃ T : Finset V, T ⊆ S ∧
      G.IsIndepSet (↑T : Set V) ∧
      2 * T.card + k ≥ S.card) :
    G.Colorable (k + 2) :=
  sorry

end
