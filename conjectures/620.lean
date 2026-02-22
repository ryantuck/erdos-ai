import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Finset

/-!
# Erdős Problem #620

The Erdős-Rogers problem: If G is a graph on n vertices without a K₄, how large a
triangle-free induced subgraph must G contain?

Let f(n) be the largest m such that every K₄-free graph on n vertices contains a triangle-free
induced subgraph with at least m vertices. It is known that f(n) = n^{1/2+o(1)}.

The best bounds currently known are:
  n^{1/2} · (log n)^{1/2} / log(log n) ≪ f(n) ≪ n^{1/2} · log n

The lower bound follows from results of Shearer [Sh95], and the upper bound was proved by
Mubayi and Verstraëte [MuVe24].

The precise asymptotic behaviour of f(n) remains open.

References: [ErRo62], [EGT92], [Er99]
-/

/--
Erdős Problem #620 (lower bound direction of the Erdős-Rogers problem):
For all ε > 0, for sufficiently large n, every K₄-free graph on n vertices
contains a triangle-free induced subgraph of size at least n^{1/2 - ε}.

Together with `erdos_problem_620_upper`, this captures f(n) = n^{1/2+o(1)}.
-/
theorem erdos_problem_620 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∀ (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
    ∃ (S : Finset (Fin n)),
      (G.induce (↑S : Set (Fin n))).CliqueFree 3 ∧
      (S.card : ℝ) ≥ (n : ℝ) ^ ((1 : ℝ) / 2 - ε) :=
  sorry

/--
Erdős Problem #620 (upper bound direction of the Erdős-Rogers problem):
For all ε > 0, for sufficiently large n, there exists a K₄-free graph on n vertices
such that every triangle-free induced subgraph has at most n^{1/2 + ε} vertices.
-/
theorem erdos_problem_620_upper :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ (G : SimpleGraph (Fin n)),
      G.CliqueFree 4 ∧
      ∀ (S : Finset (Fin n)),
        (G.induce (↑S : Set (Fin n))).CliqueFree 3 →
        (S.card : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
  sorry
