import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic

open SimpleGraph Finset

/--
Erdős Problem #23 [Er71, EFPS88, Er90, Er93, Er97b, Er97f]:

Can every triangle-free graph on 5n vertices be made bipartite by deleting
at most n² edges?

The blow-up of C₅ shows this would be best possible. The best known bound
is due to Balogh, Clemen, and Lidický [BCL21], who proved that deleting at
most 1.064n² edges suffices.

We formalise "made bipartite by deleting at most n² edges" as: there exists
a 2-colouring f such that the number of monochromatic edges is at most n².
-/
theorem erdos_problem_23 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin (5 * n))) (h : DecidableRel G.Adj),
    haveI := h
    G.CliqueFree 3 →
    ∃ (f : Fin (5 * n) → Fin 2),
      ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin (5 * n) × Fin (5 * n) =>
        p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ f p.1 = f p.2)).card ≤ n ^ 2 :=
  sorry
