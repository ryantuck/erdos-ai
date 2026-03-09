import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Metric

/--
A set S in ℝ² has all pairwise distances rational if for every two points
p, q ∈ S, the Euclidean distance ‖p - q‖ is a rational number.
-/
def AllPairwiseDistancesRational (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, dist p q = (r : ℝ)

/--
Erdős Problem #212 [Er61, Er75f, Er83c, Er87b] (Erdős–Ulam problem):

There is no dense subset of ℝ² such that all pairwise distances are rational.

Conjectured by Ulam. Erdős believed there cannot be such a set.
Tao (2014) and Shaffaf (2018) independently showed this follows from the
Bombieri–Lang conjecture: such a rational distance set must be contained
in a finite union of real algebraic curves.
-/
theorem erdos_problem_212 :
    ¬ ∃ S : Set (EuclideanSpace ℝ (Fin 2)),
      Dense S ∧ AllPairwiseDistancesRational S :=
  sorry
