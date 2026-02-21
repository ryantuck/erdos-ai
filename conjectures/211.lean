import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic

noncomputable section
open Classical

/-- Points in the Euclidean plane ℝ² -/
abbrev Point2_211 := EuclideanSpace ℝ (Fin 2)

/-- Point r lies on the line through points p and q -/
def LiesOnLine_211 (p q r : Point2_211) : Prop :=
  ∃ t : ℝ, r - p = t • (q - p)

/-- The line through two points, as a set of points -/
def lineThrough_211 (p q : Point2_211) : Set Point2_211 :=
  {r | LiesOnLine_211 p q r}

/-- The number of points in S on the line through p and q -/
noncomputable def pointsOnLine_211 (S : Finset Point2_211) (p q : Point2_211) : ℕ :=
  (S.filter (fun r => LiesOnLine_211 p q r)).card

/-- The number of distinct lines containing at least two points of S -/
noncomputable def lineCount_211 (S : Finset Point2_211) : ℕ :=
  (((S ×ˢ S).filter (fun pq => pq.1 ≠ pq.2)).image
    (fun pq => lineThrough_211 pq.1 pq.2)).card

/-!
# Erdős Problem #211

Let 1 ≤ k < n. Given n points in ℝ², at most n − k on any line,
there are ≫ kn many lines which contain at least two points.

Proved by Beck [Be83] and Szemerédi–Trotter [SzTr83].

In particular, given any 2n points with at most n on a line there
are ≫ n² many lines formed by the points.
-/

/--
Erdős Problem #211 (Proved by Beck and Szemerédi–Trotter):

There exists an absolute constant C > 0 such that for any finite set S
of points in ℝ² with |S| = n, if 1 ≤ k < n and at most n − k points
of S lie on any single line, then the number of distinct lines containing
at least two points of S is at least C · k · n.
-/
theorem erdos_problem_211 :
    ∃ C : ℝ, C > 0 ∧
      ∀ (S : Finset Point2_211) (k : ℕ),
        1 ≤ k →
        k < S.card →
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q → pointsOnLine_211 S p q ≤ S.card - k) →
        (lineCount_211 S : ℝ) ≥ C * ↑k * ↑S.card := by
  sorry
