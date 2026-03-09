import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Finset

noncomputable section

/--
The diameter of a finite set of points (maximum pairwise distance).
-/
def diameter' (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  (A.offDiag.image (fun p => dist p.1 p.2)).max'
    (by sorry) -- nonemptiness obligation

/--
All pairwise distances are at least 1.
-/
def allPairwiseDistAtLeastOne (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → dist a b ≥ 1

/--
Any two distinct pairwise distances differ by at least 1.
-/
def distinctDistancesDifferByAtLeastOne (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≠ b → c ≠ d → dist a b ≠ dist c d → |dist a b - dist c d| ≥ 1

/--
Erdős Problem #100 [Er90, Er92e, Er95, Er97f]:

Let A be a set of n points in ℝ² such that all pairwise distances are at least 1
and if two distinct pairwise distances differ then they differ by at least 1.
Is the diameter of A ≫ n?

That is, there exists an absolute constant C > 0 such that for all such sets A,
the diameter is at least C · |A|.

Kanold proved the diameter is ≥ n^(3/4). The Guth–Katz distinct distances bound
implies a lower bound of ≫ n / log n. Erdős conjectured the diameter may even be
≥ n − 1 for sufficiently large n.
-/
theorem erdos_problem_100 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        allPairwiseDistAtLeastOne A →
        distinctDistancesDifferByAtLeastOne A →
        diameter' A ≥ C * A.card :=
  sorry

end
