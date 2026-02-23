import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Classical

/--
The set of distinct distances determined by a finite point set P in ℝ².
-/
noncomputable def distinctDistances95 (P : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  ((P.product P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)

/--
The number of ordered pairs (p, q) from P with p ≠ q and dist(p, q) = d.
-/
noncomputable def distMultiplicity95 (P : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((P.product P).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = d)).card

/--
Erdős Problem #95:
Let x₁, ..., xₙ ∈ ℝ² determine the set of distances {u₁, ..., uₜ}. Suppose uᵢ
appears as the distance between f(uᵢ) many pairs of points. Then for all ε > 0,
  ∑ᵢ f(uᵢ)² ≪_ε n^{3+ε}.

This was proved by Guth and Katz (2015) who showed the stronger bound
  ∑ᵢ f(uᵢ)² ≪ n³ log n.
-/
theorem erdos_problem_95 :
    ∀ ε : ℝ, ε > 0 →
      ∃ C : ℝ, C > 0 ∧
        ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
          ((distinctDistances95 P).sum
            (fun d => (distMultiplicity95 P d) ^ 2) : ℝ) ≤
            C * (P.card : ℝ) ^ ((3 : ℝ) + ε) :=
  sorry
