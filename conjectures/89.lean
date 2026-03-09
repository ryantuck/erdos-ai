import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Real Finset

noncomputable section

/--
The set of distinct pairwise distances determined by a finite point set in ℝ².
-/
def distinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)

/--
Erdős Problem #89 [Er46b, Er57, Er61, Er75f, Er81, Er82e, Er83c, Er85, Er87b,
Er90, Er92e, Er95, Er97b, Er97c, Er97e, Er97f]:

Does every set of n distinct points in ℝ² determine ≫ n/√(log n) many distinct
distances? That is, there exists an absolute constant C > 0 such that the number
of distinct pairwise distances is at least C · n / √(log n).

A √n × √n integer grid shows that this would be best possible. Nearly solved
by Guth and Katz (2015) who proved that there are always ≫ n / log n many
distinct distances.
-/
theorem erdos_problem_89 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        (distinctDistances A).card ≥ C * A.card / Real.sqrt (Real.log A.card) :=
  sorry

end
