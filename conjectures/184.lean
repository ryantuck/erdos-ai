import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #184

Any graph on n vertices can be decomposed into O(n) many edge-disjoint cycles
and edges.

Conjectured by Erdős and Gallai [EGP66], who proved that O(n log n) many cycles
and edges suffice. The best bound is due to Bucić and Montgomery [BM22], who
prove that O(n log* n) suffice.
-/

/--
Erdős Problem #184 (Erdős-Gallai conjecture) [EGP66, Er71, Er76, Er81, Er83b]:

There exists a constant C > 0 such that for every n and every simple graph G on
n vertices, the edge set of G can be partitioned into at most C · n parts, where
each part is either a single edge or the edge set of a cycle in G.
-/
theorem erdos_problem_184 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
        (k : ℝ) ≤ C * (n : ℝ) ∧
        (∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
        (∀ i : Fin k,
          (∃ e, parts i = {e}) ∨
          (∃ (u : Fin n) (w : G.Walk u u), w.IsCycle ∧ w.edges.toFinset = parts i)) :=
  sorry

end
