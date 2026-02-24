import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal SimpleGraph

noncomputable section

namespace Erdos1174

/-!
# Erdős Problem #1174

Does there exist a graph G with no K_4 such that every edge colouring of G
with countably many colours contains a monochromatic K_3?

Does there exist a graph G with no K_{ℵ_1} such that every edge colouring of G
with countably many colours contains a monochromatic K_{ℵ_0}?

A problem of Erdős and Hajnal. Shelah proved that a graph with either property
can consistently exist.

Tags: set theory, ramsey theory
-/

/--
Erdős Problem #1174, Part 1 [Va99, 7.91]:

Does there exist a graph G with no K_4 (no 4-clique) such that for every
edge colouring of G with countably many colours (ℕ), some monochromatic K_3
(a 3-clique whose three edges all receive the same colour) exists in G?

This is an open problem of Erdős and Hajnal. Shelah proved that such a graph
can consistently exist (i.e., its existence is consistent with ZFC).
-/
theorem erdos_problem_1174a :
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ S : Finset V, ¬G.IsNClique 4 S) ∧
      ∀ (col : V → V → ℕ), (∀ u v : V, col u v = col v u) →
        ∃ (S : Finset V) (c : ℕ), G.IsNClique 3 S ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = c :=
  sorry

/--
Erdős Problem #1174, Part 2 [Va99, 7.91]:

Does there exist a graph G with no K_{ℵ_1} (no clique of cardinality ≥ ℵ_1)
such that for every edge colouring of G with countably many colours (ℕ), some
monochromatic K_{ℵ_0} exists — that is, a clique of cardinality ≥ ℵ_0 whose
edges all receive the same colour?

This is an open problem of Erdős and Hajnal. Shelah proved that such a graph
can consistently exist (i.e., its existence is consistent with ZFC).
-/
theorem erdos_problem_1174b :
    ∃ (V : Type) (G : SimpleGraph V),
      (¬∃ S : Set V, aleph 1 ≤ Cardinal.mk ↥S ∧ G.IsClique S) ∧
      ∀ (col : V → V → ℕ), (∀ u v : V, col u v = col v u) →
        ∃ (S : Set V) (c : ℕ), aleph 0 ≤ Cardinal.mk ↥S ∧ G.IsClique S ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = c :=
  sorry

end Erdos1174

end
