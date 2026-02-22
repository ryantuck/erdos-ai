import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #1018

Let ε > 0. Is there a constant C_ε such that, for all large n, every graph
on n vertices with at least n^{1+ε} edges must contain a subgraph on at most
C_ε vertices which is non-planar?

This was solved in the affirmative by Kostochka and Pyber [KoPy88], who proved
that G must contain a subdivision of K₅ (which is non-planar) with O_ε(1)
many vertices.

Tags: graph theory, planar graphs
-/

/-- A simple graph is planar if it admits a topological embedding into the
    plane without edge crossings. Defined abstractly for this conjecture. -/
def SimpleGraph.IsPlanar {V : Type*} (_ : SimpleGraph V) : Prop := sorry

/--
Erdős Problem #1018 [Er71]:

For every ε > 0, there exists a constant C (depending on ε) and a threshold
N₀ such that, for all n ≥ N₀, every simple graph on n vertices with at
least ⌈n^{1+ε}⌉ edges contains an induced subgraph on at most C vertices
which is non-planar.

Solved by Kostochka and Pyber [KoPy88].
-/
theorem erdos_problem_1018 :
    ∀ ε : ℝ, ε > 0 →
      ∃ (C N₀ : ℕ), ∀ n : ℕ, n ≥ N₀ →
        ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
          haveI := dG;
          G.edgeFinset.card ≥ ⌈(n : ℝ) ^ (1 + ε)⌉₊ →
          ∃ S : Finset (Fin n), S.card ≤ C ∧
            ¬ (G.induce (↑S : Set (Fin n))).IsPlanar :=
  sorry

end
