import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset SimpleGraph

/--
Erdős-Bollobás conjecture on Ramsey-Turán numbers (Problem #22).
Let ε > 0. For sufficiently large n, there exists a graph on n vertices
with at least n^2/8 edges, which contains no K_4, and whose largest independent set
has size at most ε * n.
-/
theorem erdos_problem_22_conjecture :
  ∀ (ε : ℝ), ε > 0 → ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
  ∃ (G : SimpleGraph (Fin n)) (h : DecidableRel G.Adj),
    haveI := h
    (G.edgeFinset.card : ℝ) ≥ (n : ℝ) ^ 2 / 8 ∧
    G.CliqueFree 4 ∧
    (∀ (s : Finset (Fin n)), Gᶜ.IsClique s → (s.card : ℝ) ≤ ε * n) :=
sorry
