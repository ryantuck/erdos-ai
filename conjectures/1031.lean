import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Classical SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #1031

If G is a graph on n vertices which contains no trivial (empty or complete)
induced subgraph on ≥ 10 log n many vertices, then G must contain an induced
non-trivial regular subgraph on ≫ log n many vertices.

A question of Erdős, Fajtlowicz, and Staton [Er93, p.340].

This was proved by Prömel and Rödl [PrRo99], who showed the stronger result
that for any c > 0, if G contains no trivial subgraph on ≥ c log n vertices
then G contains all graphs with O_c(log n) vertices as induced subgraphs.

Tags: graph theory
-/

/--
**Erdős Problem #1031** [Er93, p.340]:

If G is a graph on n vertices with no clique and no independent set of size
≥ 10 log n, then G contains an induced regular subgraph on ≥ c log n vertices
(for some absolute constant c > 0) that is neither empty nor complete.

A "trivial" subgraph means an empty or complete subgraph (i.e., an independent
set or a clique). Regularity of the induced subgraph on S means every vertex
in S has the same number of neighbors within S. Non-trivial means the common
degree d satisfies 1 ≤ d ≤ |S| - 2.
-/
theorem erdos_problem_1031 :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.CliqueFree ⌈10 * Real.log (↑n)⌉₊ →
      Gᶜ.CliqueFree ⌈10 * Real.log (↑n)⌉₊ →
      ∃ S : Finset (Fin n),
        (S.card : ℝ) ≥ c * Real.log (↑n) ∧
        ∃ d : ℕ, d ≥ 1 ∧ d + 1 < S.card ∧
          ∀ v ∈ S, (S.filter (G.Adj v)).card = d :=
  sorry

end
