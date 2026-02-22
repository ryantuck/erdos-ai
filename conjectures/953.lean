import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #953

Let A ⊂ {x ∈ ℝ² : |x| < r} be a measurable set with no integer distances,
that is, such that |a - b| ∉ ℤ for any distinct a, b ∈ A. How large can the
measure of A be?

A problem of Erdős and Sárközi. The trivial upper bound is O(r). Koizumi and
Kovac observed that Sárközy's lower bound from [466] can be adapted to give a
lower bound of ≫_ε r^{1/2-ε} for all ε > 0.

See also [465] for a similar problem (concerning upper bounds) and [466] for a
similar problem (concerning lower bounds).
-/

open MeasureTheory

noncomputable section

/-- Euclidean distance between two points in ℝ². -/
def euclidDist953 (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- A set in ℝ² has no integer distances if for every pair of distinct points
    a, b in the set, the Euclidean distance |a - b| is not an integer. -/
def NoIntegerDistances953 (A : Set (ℝ × ℝ)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ n : ℤ, euclidDist953 a b ≠ ↑n

/--
Erdős Problem #953, upper bound (trivial):

The Lebesgue measure of any measurable set A ⊂ B(0, r) in ℝ² with no integer
distances is O(r). That is, there exists an absolute constant C > 0 such that
for all r > 0 and all such A, μ(A) ≤ C · r.
-/
theorem erdos_problem_953_upper :
    ∃ C : ℝ, 0 < C ∧
    ∀ (r : ℝ), 0 < r →
    ∀ (A : Set (ℝ × ℝ)),
      MeasurableSet A →
      A ⊆ {p : ℝ × ℝ | euclidDist953 p (0, 0) < r} →
      NoIntegerDistances953 A →
      (volume A).toReal ≤ C * r :=
  sorry

/--
Erdős Problem #953, lower bound (adapted from Sárközy via [466]):

For every ε > 0, there exists c > 0 such that for all sufficiently large r,
there exists a measurable set A ⊂ B(0, r) in ℝ² with no integer distances
and μ(A) ≥ c · r^{1/2 - ε}.
-/
theorem erdos_problem_953_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
    ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ (r : ℝ), r₀ ≤ r →
    ∃ (A : Set (ℝ × ℝ)),
      MeasurableSet A ∧
      A ⊆ {p : ℝ × ℝ | euclidDist953 p (0, 0) < r} ∧
      NoIntegerDistances953 A ∧
      (volume A).toReal ≥ c * r ^ ((1 : ℝ) / 2 - ε) :=
  sorry

end
