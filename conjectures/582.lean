import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem #582

Does there exist a graph G which contains no K₄, and yet any 2-colouring
of the edges produces a monochromatic K₃?

Existence was proved by Folkman [Fo70]. These are now called Folkman numbers.
The smallest such graph has N vertices where the current best bounds are
21 ≤ N ≤ 786.

We formalize this as: there exists n and a simple graph G on Fin n that
is K₄-free, such that for any subgraph H ≤ G (representing one color class
in a 2-coloring of the edges), either H or the complementary subgraph G \ H
contains a triangle.
-/

theorem erdos_problem_582 :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.CliqueFree 4 ∧
        ∀ (H : SimpleGraph (Fin n)), H ≤ G →
          ¬H.CliqueFree 3 ∨ ¬(G \ H).CliqueFree 3 :=
  sorry
