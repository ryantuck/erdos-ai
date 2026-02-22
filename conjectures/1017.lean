import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #1017

Let f(n,k) be such that every graph on n vertices and k edges can be
partitioned into at most f(n,k) edge-disjoint complete graphs. Estimate
f(n,k) for k > n²/4.

The function f(n,k) is sometimes called the clique partition number.

Erdős, Goodman, and Pósa [EGP66] proved that f(n,k) ≤ ⌊n²/4⌋ for all k
(and in fact edges and triangles suffice), which is best possible in general,
as witnessed by a complete bipartite graph. Erdős [Er71] asks whether this
bound can be sharpened when k > n²/4.
-/

/--
Erdős Problem #1017 (Erdős–Goodman–Pósa) [Er71, EGP66]:

Every simple graph G on n vertices can be decomposed into at most ⌊n²/4⌋
edge-disjoint complete subgraphs.

Erdős asks whether this bound can be improved when the number of edges
exceeds n²/4.
-/
theorem erdos_problem_1017 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
        k ≤ n ^ 2 / 4 ∧
        (∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
        (∀ i : Fin k, ∃ (S : Finset (Fin n)),
          G.IsClique (↑S : Set (Fin n)) ∧
          parts i = S.offDiag.image (Quot.mk _)) :=
  sorry

end
