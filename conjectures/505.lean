import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded

open Metric Set

/--
Erdős Problem #505 (Borsuk's conjecture):
Is every set of diameter 1 in ℝⁿ the union of at most n+1 sets of diameter < 1?

This was originally conjectured by Borsuk in 1933. It is trivially true for n=1
and easy for n=2. Eggleston proved it for n=3. In 1981, Erdős wrote that he
suspected it was false for sufficiently high dimensions. Indeed, Kahn and Kalai
disproved it for n > 2014. The current smallest known counterexample dimension
is n = 64, due to Brouwer and Jenrich.
-/
theorem erdos_problem_505_conjecture :
  ∀ n : ℕ, ∀ S : Set (EuclideanSpace ℝ (Fin n)),
    Metric.diam S = 1 →
    ∃ F : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin n)),
      S = ⋃ i, F i ∧ ∀ i, Metric.diam (F i) < 1 :=
sorry
