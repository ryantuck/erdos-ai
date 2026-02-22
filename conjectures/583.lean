import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #583

Every connected graph on n vertices can be partitioned into at most ⌈n/2⌉
edge-disjoint paths.

A problem of Erdős and Gallai [ErGa59].
-/

/--
Erdős Problem #583 [ErGa59]:

Every connected graph on n vertices can be partitioned into at most ⌈n/2⌉
edge-disjoint paths.
-/
theorem erdos_problem_583 (n : ℕ) (G : SimpleGraph (Fin n))
    (dG : DecidableRel G.Adj) (hconn : G.Connected) :
    haveI := dG
    ∃ (k : ℕ) (paths : Fin k → Σ (v w : Fin n), G.Walk v w),
      k ≤ (n + 1) / 2 ∧
      (∀ i, (paths i).2.2.IsPath) ∧
      (∀ i j : Fin k, i ≠ j →
        Disjoint (paths i).2.2.edges.toFinset (paths j).2.2.edges.toFinset) ∧
      (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ (paths i).2.2.edges.toFinset) :=
  sorry

end
