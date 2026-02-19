import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Subgraph

open SimpleGraph

/--
Erdős Problem #108 (Erdős-Hajnal conjecture on chromatic number and girth):
For every r ≥ 4 and k ≥ 2, there exists a finite f(k, r) such that every graph G
with chromatic number at least f(k, r) contains a subgraph H of girth at least r
and chromatic number at least k.

Conjectured by Erdős and Hajnal. Rödl proved the r = 4 case [Ro77].
Here egirth is the extended girth (in ℕ∞), which equals ⊤ for acyclic graphs and
otherwise equals the length of the shortest cycle.
-/
theorem erdos_problem_108 :
    ∀ (r k : ℕ), 4 ≤ r → 2 ≤ k →
      ∃ (f : ℕ),
        ∀ (V : Type*) (G : SimpleGraph V),
          (f : ℕ∞) ≤ G.chromaticNumber →
          ∃ H : G.Subgraph,
            (k : ℕ∞) ≤ H.coe.chromaticNumber ∧
            (r : ℕ∞) ≤ H.coe.egirth :=
  sorry
