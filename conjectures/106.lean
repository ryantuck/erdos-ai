import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open BigOperators Real

/--
A square placement in ℝ²: a center point, a positive side length, and a
rotation angle (in radians) measuring how far the square is rotated from
the standard axis-aligned orientation.
-/
structure SquarePlacement where
  center : ℝ × ℝ
  side   : ℝ
  angle  : ℝ
  side_pos : 0 < side

/--
The closed region occupied by a square placement.  A point p lies in the
region iff, when translated so the center is at the origin and then rotated
by `-angle`, its coordinates both lie in `[-side/2, side/2]`.
-/
noncomputable def SquarePlacement.region (sq : SquarePlacement) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ |
    let u :=  (p.1 - sq.center.1) * cos sq.angle + (p.2 - sq.center.2) * sin sq.angle
    let v := -(p.1 - sq.center.1) * sin sq.angle + (p.2 - sq.center.2) * cos sq.angle
    |u| ≤ sq.side / 2 ∧ |v| ≤ sq.side / 2}

/--
The open interior of a square placement (strict inequalities).
-/
noncomputable def SquarePlacement.sqInterior (sq : SquarePlacement) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ |
    let u :=  (p.1 - sq.center.1) * cos sq.angle + (p.2 - sq.center.2) * sin sq.angle
    let v := -(p.1 - sq.center.1) * sin sq.angle + (p.2 - sq.center.2) * cos sq.angle
    |u| < sq.side / 2 ∧ |v| < sq.side / 2}

/--
The unit square [0,1]² ⊆ ℝ².
-/
def unitSquare : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/--
A valid configuration of `n` squares inside the unit square:
1. Each square's closed region is contained in the unit square.
2. No two distinct squares share an interior point (their open interiors
   are disjoint).
-/
def IsValidSquareConfig (n : ℕ) (config : Fin n → SquarePlacement) : Prop :=
  (∀ i : Fin n, (config i).region ⊆ unitSquare) ∧
  (∀ i j : Fin n, i ≠ j → Disjoint (config i).sqInterior (config j).sqInterior)

/--
`f n` is the supremum of the total side-length sum over all valid configurations
of `n` (possibly rotated) squares inside the unit square with pairwise disjoint
interiors.
-/
noncomputable def f (n : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ config : Fin n → SquarePlacement,
    IsValidSquareConfig n config ∧ s = ∑ i : Fin n, (config i).side}

/--
Erdős Problem #106:

Draw `n` squares (not necessarily axis-aligned) inside the unit square [0,1]²
with no two squares sharing a common interior point.  Let `f(n)` be the maximum
possible sum of the side-lengths of the squares.

**Conjecture**: `f(k² + 1) = k` for every positive integer `k`.

Background:
- It follows easily from the Cauchy–Schwarz inequality that `f(k²) = k`.
- The lower bound `f(k² + 1) ≥ k` is elementary: subdivide [0,1]² into k²
  squares of side 1/k, then replace any one of them by two squares of side
  1/(2k); the total side-length is (k² − 1)/k + 2·(1/(2k)) = k.
- The conjecture asserts that this lower bound is tight: no configuration of
  k² + 1 squares can exceed the total side-length k achievable with k² squares.
- Baek, Koizumi, and Ueoro (2024) proved the axis-aligned variant: if all
  squares are required to have sides parallel to the coordinate axes, then the
  supremum equals k.
-/
theorem erdos_problem_106 :
    ∀ k : ℕ, 0 < k → f (k ^ 2 + 1) = (k : ℝ) :=
  sorry
