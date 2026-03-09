import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Real Finset

noncomputable section

/--
The number of unit-distance pairs in a finite point set in ℝ²:
the number of ordered pairs (p, q) with p ≠ q and dist(p, q) = 1.
We count ordered pairs; the conjecture bound applies equally
(up to a factor of 2) to unordered pairs.
-/
def unitDistancePairs (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)).card

/--
Erdős Problem #90 [Er46b, Er61, Er75f, Er81, Er82e, Er83c, Er85, Er90, Er94b,
Er95, Er97c, Er97e, Er97f]:

Does every set of n distinct points in ℝ² contain at most n^{1+O(1/log log n)}
many pairs which are distance 1 apart?

Equivalently, there exists a constant C > 0 such that for every finite set A
of points in ℝ², the number of unit-distance pairs is at most
|A|^{1 + C / log(log |A|)}.

The best known upper bound is O(n^{4/3}), due to Spencer, Szemerédi, and
Trotter (1984). A √n × √n section of the integer lattice shows that
n^{1+c/log log n} pairs are achievable.
-/
theorem erdos_problem_90 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        2 ≤ A.card →
        (unitDistancePairs A : ℝ) ≤
          (A.card : ℝ) ^ (1 + C / Real.log (Real.log (A.card : ℝ))) :=
  sorry

end
