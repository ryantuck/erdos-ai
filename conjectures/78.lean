import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

open SimpleGraph

/--
Erdős Problem #78 (Open, $100 prize):

Let R(k) be the Ramsey number for K_k, the minimal n such that every
2-colouring of the edges of K_n contains a monochromatic copy of K_k.
Give a constructive proof that R(k) > C^k for some constant C > 1.

Erdős gave a simple probabilistic (non-constructive) proof that
R(k) ≫ k · 2^{k/2}. This problem asks for an explicit/constructive
lower bound that is still exponential in k.

Equivalently, this asks for an explicit construction of a graph on n
vertices which does not contain any clique or independent set of size
≥ c · log(n) for some constant c > 0.

We formalize the core mathematical content: there exists C > 1 such that
for all k ≥ 2, there exists a graph on at least C^k vertices with no
clique or independent set of size k (an independent set of size k in G
is a clique of size k in Gᶜ). The "constructive" requirement pertains
to the nature of the proof, not the formal statement itself.
-/
theorem erdos_problem_78 :
    ∃ C : ℝ, C > 1 ∧ ∀ k : ℕ, k ≥ 2 →
      ∃ n : ℕ, (C ^ k : ℝ) ≤ ↑n ∧
        ∃ G : SimpleGraph (Fin n),
          G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
  sorry
