import Mathlib.Topology.MetricSpace.Basic

open Metric

/--
A colouring of ℝ² with `k` colours is a function from ℝ × ℝ to `Fin k`.
-/
abbrev Colouring (k : ℕ) := ℝ × ℝ → Fin k

/--
A colouring is **proper** for the unit-distance graph on ℝ² if no two points
at Euclidean distance exactly 1 receive the same colour.
-/
def ProperUnitDistanceColouring (k : ℕ) (c : Colouring k) : Prop :=
  ∀ p q : ℝ × ℝ, dist p q = 1 → c p ≠ c q

/--
There exists a proper colouring of the plane with `k` colours.
-/
def PlaneColourable (k : ℕ) : Prop :=
  ∃ c : Colouring k, ProperUnitDistanceColouring k c

/--
Erdős Problem #508 [Er61, Er75f, Er81]:

What is the chromatic number of the plane? That is, what is the smallest
number of colours required to colour ℝ² such that no two points of the same
colour are distance 1 apart?

This is the Hadwiger–Nelson problem. The best bounds currently known are
5 ≤ χ ≤ 7. The lower bound is due to de Grey (2018). The upper bound can be
seen by colouring the plane by tessellating with hexagons of diameter slightly
less than 1.

The conjecture asks to determine the exact value. We state the known bounds:
the plane is 7-colourable, and it is not 4-colourable.
-/
theorem erdos_problem_508 :
    PlaneColourable 7 ∧ ¬ PlaneColourable 4 :=
  sorry
