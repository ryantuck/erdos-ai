import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #641

Is there some function f such that for all k ≥ 1 if a finite graph G has
chromatic number ≥ f(k) then G has k edge-disjoint cycles on the same set
of vertices?

A problem of Erdős and Hajnal [Er92b][Er97d, p.84].

This was resolved in the negative by Janzer, Steiner, and Sudakov [JSS24] -
in fact, this fails even at k = 2. They proved that there exists a constant
c > 0 such that, for all large n, there exists a graph on n vertices with
chromatic number ≥ c(log log n)/(log log log n) which contains no 4-regular
subgraph.
-/

/--
**Erdős Problem #641** (Original conjecture, DISPROVED) [Er92b][Er97d, p.84]:

For every k ≥ 1, there exists f(k) such that every finite graph with
chromatic number at least f(k) contains k edge-disjoint cycles on the
same vertex set.
-/
theorem erdos_problem_641 :
    ∀ k : ℕ, 1 ≤ k →
      ∃ f : ℕ,
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          (f : ℕ∞) ≤ G.chromaticNumber →
          ∃ (cycles : Fin k → Σ (v : Fin n), G.Walk v v),
            (∀ i, (cycles i).2.IsCycle) ∧
            (∀ i j, (cycles i).2.support.toFinset = (cycles j).2.support.toFinset) ∧
            (∀ i j, i ≠ j →
              Disjoint (cycles i).2.edges.toFinset (cycles j).2.edges.toFinset) :=
  sorry

/--
**Erdős Problem #641** (Disproof, Janzer–Steiner–Sudakov [JSS24]):

There exists k ≥ 1 such that for any proposed bound f, one can find a
finite graph with chromatic number at least f but without k edge-disjoint
cycles on any common vertex set. In fact k = 2 already fails.
-/
theorem erdos_problem_641_disproof :
    ∃ k : ℕ, 1 ≤ k ∧
      ∀ f : ℕ,
        ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
          (f : ℕ∞) ≤ G.chromaticNumber ∧
          ¬∃ (cycles : Fin k → Σ (v : Fin n), G.Walk v v),
            (∀ i, (cycles i).2.IsCycle) ∧
            (∀ i j, (cycles i).2.support.toFinset = (cycles j).2.support.toFinset) ∧
            (∀ i j, i ≠ j →
              Disjoint (cycles i).2.edges.toFinset (cycles j).2.edges.toFinset) :=
  sorry

end
