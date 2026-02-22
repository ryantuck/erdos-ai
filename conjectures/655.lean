import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/--
A finite set of points in ℝ² satisfies the "no three equidistant from a center"
condition if for each point p in the set, no three other distinct points in the
set are equidistant from p (i.e., no circle centered at p passes through three
or more other points).
-/
def NoThreeEquidistantFromCenter (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, ∀ q₁ ∈ P, ∀ q₂ ∈ P, ∀ q₃ ∈ P,
    p ≠ q₁ → p ≠ q₂ → p ≠ q₃ →
    q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
    ¬(dist p q₁ = dist p q₂ ∧ dist p q₂ = dist p q₃)

/--
The number of distinct pairwise distances determined by a finite point set in ℝ².
-/
noncomputable def distinctDistanceCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {d : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ d = dist p q}

/--
Erdős Problem #655 (Erdős-Pach):
Let x₁, ..., xₙ ∈ ℝ² be such that no circle whose centre is one of the xᵢ
contains three other points. Then the number of distinct distances determined
by the points is at least (1 + c) · n/2 for some constant c > 0 and all n
sufficiently large.
-/
theorem erdos_problem_655 :
  ∃ c : ℝ, c > 0 ∧
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        NoThreeEquidistantFromCenter P →
        (distinctDistanceCount P : ℝ) ≥ (1 + c) * (n : ℝ) / 2 :=
sorry
