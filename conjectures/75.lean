import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Cardinal

noncomputable section

/-!
# Erdős Problem #75

Is there a graph of chromatic number ℵ₁ with ℵ₁ vertices such that for all
ε > 0, if n is sufficiently large and H is a subgraph on n vertices, then H
contains an independent set of size > n^{1-ε}?

What about an independent set of size ≫ n (i.e., of linear size)?

Conjectured by Erdős, Hajnal, and Szemerédi [EHS82].
-/

/--
Erdős Problem #75, Part 1 [EHS82,p.120][Er95,p.11][Er95d,p.63]:

There exists a graph G on ℵ₁ vertices with chromatic number ℵ₁ such that for
all ε > 0, if n is sufficiently large and S is any set of n vertices, then
S contains an independent set of size > n^{1-ε}.
-/
theorem erdos_problem_75a :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      #V = aleph 1 ∧
      ¬Nonempty (G.Coloring ℕ) ∧
      ∀ ε : ℝ, ε > 0 →
        ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
          ∀ S : Finset V, S.card = n →
            ∃ T : Finset V, T ⊆ S ∧
              (↑T : Set V).Pairwise (fun u v => ¬G.Adj u v) ∧
              (T.card : ℝ) > (n : ℝ) ^ ((1 : ℝ) - ε) :=
  sorry

/--
Erdős Problem #75, Part 2 [EHS82,p.120][Er95,p.11][Er95d,p.63]:

There exists a graph G on ℵ₁ vertices with chromatic number ℵ₁ such that
there exists c > 0 where every set of n ≥ 1 vertices contains an independent
set of size at least c · n.
-/
theorem erdos_problem_75b :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      #V = aleph 1 ∧
      ¬Nonempty (G.Coloring ℕ) ∧
      ∃ c : ℝ, c > 0 ∧
        ∀ n : ℕ, n ≥ 1 →
          ∀ S : Finset V, S.card = n →
            ∃ T : Finset V, T ⊆ S ∧
              (↑T : Set V).Pairwise (fun u v => ¬G.Adj u v) ∧
              (T.card : ℝ) ≥ c * (n : ℝ) :=
  sorry

end
