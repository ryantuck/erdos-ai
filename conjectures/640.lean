import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Paths

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #640

Let k ≥ 3. Does there exist some f(k) such that if a graph G has chromatic number
≥ f(k) then G must contain some odd cycle whose vertices span a graph of chromatic
number ≥ k?

A problem of Erdős and Hajnal [Er97d, p.84].

This is trivial when k = 3, since any non-bipartite graph contains an odd cycle,
and all odd cycles have chromatic number 3.
-/

/--
Erdős Problem #640 (Erdős-Hajnal) [Er97d, p.84]:

For every k ≥ 3, there exists f(k) such that every graph with chromatic number
at least f(k) contains an odd cycle whose vertices span an induced subgraph
with chromatic number at least k.
-/
theorem erdos_problem_640 :
    ∀ k : ℕ, 3 ≤ k →
      ∃ f : ℕ,
        ∀ (V : Type*) (G : SimpleGraph V),
          (f : ℕ∞) ≤ G.chromaticNumber →
          ∃ (v : V) (p : G.Walk v v),
            p.IsCycle ∧ Odd p.length ∧
            (k : ℕ∞) ≤ (G.induce {w : V | w ∈ p.support}).chromaticNumber :=
  sorry

end
