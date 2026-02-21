import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card

noncomputable section

open Finset

/-- All points in S lie on a common circle with positive radius. -/
def AllOnCircle (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, 0 < r ∧ ∀ p ∈ S, dist p c = r

/-- All points in S are collinear: they lie on a common affine line. -/
def AllCollinear (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ a b : EuclideanSpace ℝ (Fin 2), a ≠ b ∧
    ∀ p ∈ S, ∃ t : ℝ, p = a + t • (b - a)

/-- The number of distinct circles determined by S. A circle is identified by its
center and positive radius. It is "determined" by S if at least 3 points of S
lie on it. -/
def numDeterminedCircles (S : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {p : EuclideanSpace ℝ (Fin 2) × ℝ |
    0 < p.2 ∧ 3 ≤ Set.ncard {q ∈ (↑S : Set (EuclideanSpace ℝ (Fin 2))) | dist q p.1 = p.2}}

/--
Erdős Problem #506 [Er61, p.245]:

What is the minimum number of circles determined by n points in ℝ², not all on a
circle (and not all on a line)?

Elliott [El67] proved that for n > 393 points not all on a circle or a line, the
points determine at least C(n-1, 2) distinct circles. Purdy and Smith [PuSm]
corrected this to the sharper bound C(n-1, 2) + 1 - ⌊(n-1)/2⌋, which is best
possible (witnessed by n-1 points on a circle and one point off it).
-/
theorem erdos_problem_506 (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hn : 393 < S.card)
    (hnotcirc : ¬AllOnCircle S)
    (hnotcol : ¬AllCollinear S) :
    Nat.choose (S.card - 1) 2 + 1 - (S.card - 1) / 2 ≤ numDeterminedCircles S :=
  sorry
