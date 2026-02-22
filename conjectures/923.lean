import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Subgraph

open SimpleGraph

/--
Erdős Problem #923:
Is it true that, for every k, there is some f(k) such that if G has chromatic number
≥ f(k) then G contains a triangle-free subgraph with chromatic number ≥ k?

Proved by Rödl [Ro77]. This is the r = 4 special case of problem #108.
Triangle-free is formalized here as girth ≥ 4 (no cycles of length 3).
-/
theorem erdos_problem_923 :
    ∀ (k : ℕ), 2 ≤ k →
      ∃ (f : ℕ),
        ∀ (V : Type*) (G : SimpleGraph V),
          (f : ℕ∞) ≤ G.chromaticNumber →
          ∃ H : G.Subgraph,
            (k : ℕ∞) ≤ H.coe.chromaticNumber ∧
            (4 : ℕ∞) ≤ H.coe.egirth :=
  sorry
