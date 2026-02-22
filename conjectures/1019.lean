import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph Finset

noncomputable section

namespace Erdos1019

/-!
# Erdős Problem #1019

A planar graph on n vertices with 3n-6 edges (the maximum possible) is called
saturated (or maximal planar). Does every graph on n vertices with
⌊n²/4⌋ + ⌊(n+1)/2⌋ edges contain a saturated planar graph with >3 vertices?

A saturated planar graph on 3 vertices is a triangle, which by Turán's theorem
is contained in every graph on n vertices with ⌊n²/4⌋ + 1 edges. Erdős writes
it is 'easy to construct' a graph on n vertices with ⌊n²/4⌋ + ⌊(n-1)/2⌋ edges
which contains no saturated planar graph with >3 vertices.

This was proved in the affirmative by Simonovits in his PhD thesis: every such
graph must contain either a K₄ or C_l + 2K₁ for some l ≥ 3.

Tags: graph theory, planar graphs
-/

/-- A simple graph is planar if it admits a topological embedding into the
    plane without edge crossings. Defined abstractly here. -/
def IsPlanar {V : Type*} (_ : SimpleGraph V) : Prop := sorry

/--
Erdős Problem #1019 [Er64f, Er69c, Er71]:

Every graph on n ≥ 4 vertices with at least ⌊n²/4⌋ + ⌊(n+1)/2⌋ edges
contains a maximal planar subgraph (planar with exactly 3k - 6 edges)
on some k > 3 vertices.

Proved by Simonovits.
-/
theorem erdos_problem_1019 :
    ∀ n : ℕ, n ≥ 4 →
      ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
        haveI := dG;
        G.edgeFinset.card ≥ n ^ 2 / 4 + (n + 1) / 2 →
        ∃ (k : ℕ) (_ : k > 3) (H : SimpleGraph (Fin k))
          (dH : DecidableRel H.Adj) (f : Fin k → Fin n),
          haveI := dH;
          Function.Injective f ∧
          (IsPlanar H ∧ H.edgeFinset.card = 3 * k - 6) ∧
          ∀ u v, H.Adj u v → G.Adj (f u) (f v) :=
  sorry

end Erdos1019

end
