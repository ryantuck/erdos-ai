import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Real Finset

noncomputable section

/--
For a point `x` and a finite set `A` in ℝ², the maximum number of other points
in `A` that are all at the same distance from `x`.
-/
def maxEquidistantCount (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  A.sup (fun y => (A.filter (fun z => z ≠ x ∧ dist x z = dist x y)).card)

/--
Erdős Problem #92 [Er75f, Er94b, Er95, Er97c]:

Let f(n) be maximal such that there exists a set A of n points in ℝ² in which
every x ∈ A has at least f(n) points in A equidistant from x.

Is it true that f(n) ≤ n^{O(1/log log n)}? That is, there exists a constant C > 0
such that for every finite set A of n ≥ 2 points in ℝ², if every point of A has
at least k other points equidistant from it, then k ≤ n^{C / log log n}.

The set of lattice points shows f(n) > n^{c/log log n} for some c > 0.
Erdős offered $500 for a proof that f(n) ≤ n^{o(1)}.
-/
theorem erdos_problem_92 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        2 ≤ A.card →
        ∀ x ∈ A,
          (maxEquidistantCount A x : ℝ) ≤
            (A.card : ℝ) ^ (C / Real.log (Real.log (A.card : ℝ))) :=
  sorry

end
