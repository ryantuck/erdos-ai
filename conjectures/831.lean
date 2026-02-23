import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

namespace Erdos831

/--
A finite point set in ℝ² has no three collinear if every three-element subset
is not collinear (i.e., no line contains three or more of the points).
-/
def NoThreeCollinear (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 3 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
Four points in ℝ² are concyclic if they all lie on a common circle, i.e.,
there exists a center and positive radius such that all four points are
equidistant from the center.
-/
def FourPointsConcyclic (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, r > 0 ∧ ∀ p ∈ S, dist p c = r

/--
A finite point set in ℝ² has no four concyclic if every four-element subset
does not lie on a common circle.
-/
def NoFourConcyclic (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 4 → ¬FourPointsConcyclic S

/--
The number of distinct circumradii of circles passing through three points of P.
A radius r is counted if there exist three distinct points a, b, c in P and a
center o such that all three points lie on the circle of radius r centered at o.
-/
noncomputable def distinctCircumradiiCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {r : ℝ | r > 0 ∧ ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P,
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    ∃ o : EuclideanSpace ℝ (Fin 2), dist a o = r ∧ dist b o = r ∧ dist c o = r}

/--
Erdős Problem #831:
Let h(n) be maximal such that in any n points in ℝ² (with no three on a line
and no four on a circle) there are at least h(n) many circles of different radii
passing through three points. Estimate h(n).

Formalized as: h(n) → ∞, i.e., for every C there exists N such that for all
n ≥ N and every set P of n points in ℝ² in general position (no three collinear,
no four concyclic), the number of distinct circumradii of circles through three
points is at least C.
-/
theorem erdos_problem_831 :
  ∀ C : ℕ,
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        NoThreeCollinear P →
        NoFourConcyclic P →
        distinctCircumradiiCount P ≥ C :=
  sorry

end Erdos831
