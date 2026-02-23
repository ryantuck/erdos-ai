import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Algebra.Ring.Subring.Basic

noncomputable section

open MeasureTheory

/--
Erdős Problem #1154 [Er79h, p.119]:

Does there exist, for every α ∈ [0,1], a subring of ℝ with Hausdorff dimension α?

Erdős and Volkmann proved the analogous result for subgroups of ℝ.
Falconer showed that any subring with Hausdorff dimension α ∈ (1/2,1) cannot be
Borel or Suslin. Edgar and Miller proved that any Borel or analytic subring of ℝ
either has Hausdorff dimension 0 or equals ℝ. Mauldin proved the result for
subfields assuming the continuum hypothesis.
-/
theorem erdos_problem_1154 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ S : Subring ℝ, dimH (↑S : Set ℝ) = ENNReal.ofReal α :=
  sorry

end
