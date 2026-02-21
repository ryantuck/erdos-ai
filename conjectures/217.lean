import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod

noncomputable section
open Classical

/-!
# Erdős Problem #217

For which n are there n points in ℝ², no three on a line and no four on a
circle, which determine n-1 distinct distances and so that (in some ordering
of the distances) the i-th distance occurs i times?

An example with n=4 is an isosceles triangle with the point in the centre.
Erdős originally believed this was impossible for n ≥ 5, but Pomerance
constructed a set with n = 5, and Palásti proved such sets exist for all n ≤ 8.
Erdős believed this is impossible for all sufficiently large n.
-/

/-- Three points in ℝ² are collinear if the cross product of (q - p) and (r - p)
    vanishes, i.e. the signed area of the triangle is zero. -/
def Collinear3 (p q r : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (q 0 - p 0) * (r 1 - p 1) = (q 1 - p 1) * (r 0 - p 0)

/-- A finite point set in ℝ² has no three collinear points. -/
def NoThreeCollinear (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r → ¬Collinear3 p q r

/-- Four points in ℝ² are concyclic if they are all equidistant from some center. -/
def Concyclic4 (p₁ p₂ p₃ p₄ : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
    dist p₁ c = r ∧ dist p₂ c = r ∧ dist p₃ c = r ∧ dist p₄ c = r

/-- A finite point set in ℝ² has no four concyclic points. -/
def NoFourConcyclic (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p₁ ∈ S, ∀ p₂ ∈ S, ∀ p₃ ∈ S, ∀ p₄ ∈ S,
    p₁ ≠ p₂ → p₁ ≠ p₃ → p₁ ≠ p₄ → p₂ ≠ p₃ → p₂ ≠ p₄ → p₃ ≠ p₄ →
    ¬Concyclic4 p₁ p₂ p₃ p₄

/-- A set S of n points has the distance multiplicity property if there exist n-1
    distinct pairwise distances such that (in some ordering) the j-th distance
    occurs exactly j times as an unordered pair. We count ordered pairs from
    S.offDiag, so the j-th distance yields 2*(j+1) ordered pairs (since
    Fin (n-1) is 0-indexed). -/
def HasDistanceMultiplicityProperty (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ (d : Fin (S.card - 1) → ℝ),
    Function.Injective d ∧
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ i, dist p q = d i) ∧
    (∀ i : Fin (S.card - 1),
      (S.offDiag.filter (fun pq => dist pq.1 pq.2 = d i)).card = 2 * (i.val + 1))

/--
Erdős Conjecture (Problem #217) [Er83c, Er87b, Er97e]:

For all sufficiently large n, there does not exist a set of n points in ℝ²,
no three on a line and no four on a circle, which determine n-1 distinct
distances such that (in some ordering) the i-th distance occurs exactly i times.

Known: such configurations exist for all n ≤ 8 (Palásti). Erdős conjectured
this is impossible for all sufficiently large n.
-/
theorem erdos_problem_217 :
    ∃ N₀ : ℕ, ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))),
      N₀ ≤ S.card →
      NoThreeCollinear S →
      NoFourConcyclic S →
      ¬HasDistanceMultiplicityProperty S :=
  sorry

end
