import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem #595

Is there an infinite graph $G$ which contains no $K_4$ and is not the union
of countably many triangle-free graphs?

A problem of Erdős and Hajnal. Folkman [Fo70] and Nešetřil and Rödl [NeRo75]
have proved that for every $n \geq 1$ there is a graph $G$ which contains no
$K_4$ and is not the union of $n$ triangle-free graphs.

https://www.erdosproblems.com/595
-/

/--
Erdős Problem #595 [Er87]:

There exists an infinite graph G which is K₄-free and whose edge set cannot
be covered by countably many triangle-free subgraphs.
-/
theorem erdos_problem_595 :
    ∃ (V : Type) (_ : Infinite V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧
        ¬∃ (H : ℕ → SimpleGraph V),
          (∀ i, H i ≤ G) ∧
          (∀ i, (H i).CliqueFree 3) ∧
          (∀ u v, G.Adj u v → ∃ i, (H i).Adj u v) :=
  sorry
