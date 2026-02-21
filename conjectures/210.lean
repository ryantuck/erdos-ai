import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic

noncomputable section
open Classical

/-- Points in the Euclidean plane ℝ² -/
abbrev Point2_210 := EuclideanSpace ℝ (Fin 2)

/-- Point r lies on the line through distinct points p and q -/
def LiesOnLine_210 (p q r : Point2_210) : Prop :=
  ∃ t : ℝ, r - p = t • (q - p)

/-- A finite set of points is not all collinear: there exist three
    non-collinear points in S -/
def NotAllCollinear_210 (S : Finset Point2_210) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ ¬LiesOnLine_210 p q r

/-- An ordered pair (p, q) determines an ordinary line for S if p ≠ q,
    both lie in S, and no third point of S lies on the line through p and q -/
def IsOrdinaryPair_210 (S : Finset Point2_210) (p q : Point2_210) : Prop :=
  p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ ∀ r ∈ S, r ≠ p → r ≠ q → ¬LiesOnLine_210 p q r

/-- The number of ordinary lines determined by S.
    Counts ordered pairs forming ordinary lines and divides by 2. -/
noncomputable def ordinaryLineCount_210 (S : Finset Point2_210) : ℕ :=
  ((S ×ˢ S).filter (fun pq => IsOrdinaryPair_210 S pq.1 pq.2)).card / 2

/--
Erdős Problem #210 (Proved by Green-Tao):
Let f(n) be minimal such that for any n points in ℝ², not all on a line,
there are at least f(n) ordinary lines (lines containing exactly 2 of the
points). Green and Tao proved that f(n) ≥ n/2 for all sufficiently large n,
resolving the conjecture of Erdős and de Bruijn and strengthening earlier
results of Motzkin (f(n) → ∞), Kelly-Moser (f(n) ≥ 3n/7), and
Csima-Sawyer (f(n) ≥ 6n/13).
-/
theorem erdos_problem_210 :
    ∃ N₀ : ℕ, ∀ (S : Finset Point2_210),
      S.card ≥ N₀ →
      NotAllCollinear_210 S →
      ordinaryLineCount_210 S ≥ S.card / 2 :=
  sorry
