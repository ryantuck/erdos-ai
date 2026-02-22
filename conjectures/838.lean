import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open Classical Filter Real Finset

/--
A finite point set P in ℝ² is in general position if no three of its points
are collinear.
-/
def InGeneralPosition838 (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 3 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
A finite point set S in ℝ² is in convex position if no point of S lies in
the convex hull of the remaining points.
-/
def InConvexPosition838 (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, p ∉ convexHull ℝ (↑(S.erase p) : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of subsets of P that are in convex position.
-/
noncomputable def numConvexSubsets838 (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.powerset.filter fun S => InConvexPosition838 S).card

/--
f(n) is the minimum number of convex subsets determined by any n points in ℝ²
in general position (no three collinear).
-/
noncomputable def f838 (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n ∧ InGeneralPosition838 P ∧ numConvexSubsets838 P = k}

/--
Erdős Problem #838 (Erdős-Hammer):
Let f(n) be the maximum number such that any n points in ℝ², with no three
collinear, determine at least f(n) different convex subsets. Does there exist
a constant c such that
  lim_{n → ∞} log(f(n)) / (log n)² = c?

Erdős proved that n^{c₁ log n} < f(n) < n^{c₂ log n} for some constants
c₁, c₂ > 0 [Er78c].
-/
theorem erdos_problem_838 :
    ∃ c : ℝ, Tendsto (fun n : ℕ => Real.log (f838 n : ℝ) / (Real.log (n : ℝ)) ^ 2)
      atTop (nhds c) :=
  sorry

end
