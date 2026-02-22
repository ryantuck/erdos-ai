import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Metric

/--
All pairwise distances in a finite point set are separated by at least 1:
for any two distinct unordered pairs {a, b} and {c, d} of points from A
(where a ≠ b and c ≠ d), |dist(a, b) - dist(c, d)| ≥ 1.
-/
def AllPairwiseDistancesDifferByOne {X : Type*} [PseudoMetricSpace X]
    (A : Finset X) : Prop :=
  ∀ a b c d : X, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≠ b → c ≠ d →
    (a ≠ c ∨ b ≠ d) → (a ≠ d ∨ b ≠ c) →
    |dist a b - dist c d| ≥ 1

/--
Erdős Problem #670:
Let A ⊆ ℝ^d be a set of n points such that all pairwise distances differ by
at least 1. Is the diameter of A at least (1 + o(1))n²?

The lower bound of C(n,2) for the diameter is trivial. Erdős [Er97f] proved
the claim when d = 1.

Formalized as: for every ε > 0, there exists N such that for all n ≥ N, for
every dimension d and every set A of n points in ℝ^d with all pairwise
distances differing by at least 1, the diameter of A is at least (1 - ε) · n².
-/
theorem erdos_problem_670 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ d : ℕ,
          ∀ A : Finset (EuclideanSpace ℝ (Fin d)),
            A.card = n →
            AllPairwiseDistancesDifferByOne A →
            (1 - ε) * (n : ℝ) ^ 2 ≤
              Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) :=
  sorry
