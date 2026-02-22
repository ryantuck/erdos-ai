import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph Finset

/-!
# Erdős Problem #916

Does every graph with n vertices and 2n-2 edges contain a cycle and another
vertex adjacent to three vertices on the cycle?

This would be a stronger form of Dirac's result [Di60] that every such graph
contains a subgraph homeomorphic to K₄.

The answer is yes, as proved by Thomassen [Th74].
-/

/--
Erdős Problem #916 [Er67b]:

Every simple graph with n vertices and at least 2n-2 edges contains a cycle C
and a vertex v not on C that is adjacent to at least three vertices of C.

A cycle of length m (m ≥ 3) is represented as an injective map
`cycle : Fin m → Fin n` where consecutive vertices (including wrap-around)
are adjacent.
-/
theorem erdos_problem_916 (n : ℕ) (hn : n ≥ 4)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : G.edgeFinset.card ≥ 2 * n - 2) :
    ∃ (k : ℕ) (cycle : Fin (k + 3) → Fin n),
      Function.Injective cycle ∧
      (∀ i : Fin (k + 3), G.Adj (cycle i)
        (cycle ⟨(i.val + 1) % (k + 3), Nat.mod_lt _ (by omega)⟩)) ∧
      ∃ v : Fin n, v ∉ Set.range cycle ∧
        ∃ (i j l : Fin (k + 3)), i ≠ j ∧ j ≠ l ∧ i ≠ l ∧
          G.Adj v (cycle i) ∧ G.Adj v (cycle j) ∧ G.Adj v (cycle l) :=
  sorry
