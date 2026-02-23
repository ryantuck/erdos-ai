import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

noncomputable section

namespace Erdos1166

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A step distribution for a simple random walk on ℤ²: the random variable takes
    values in {(1,0), (-1,0), (0,1), (0,-1)} each with equal probability. -/
def IsUniformStep (μ : Measure Ω) (X : Ω → ℤ × ℤ) : Prop :=
  (∀ ω, X ω ∈ ({((1 : ℤ), 0), (-1, 0), (0, 1), (0, -1)} : Set (ℤ × ℤ))) ∧
  μ {ω | X ω = (1, 0)} = μ {ω | X ω = (-1, 0)} ∧
  μ {ω | X ω = (-1, 0)} = μ {ω | X ω = (0, 1)} ∧
  μ {ω | X ω = (0, 1)} = μ {ω | X ω = (0, -1)}

/-- Position of the random walk at time n: S_n = X₀ + X₁ + ⋯ + X_{n-1},
    starting at the origin S₀ = (0, 0). -/
def walkPosition (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : ℤ × ℤ :=
  ∑ i ∈ Finset.range n, X i ω

/-- The local time (visit count) at site x up to time k:
    f_k(x) = |{l : 0 ≤ l ≤ k | S_l = x}|. -/
def localTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (k : ℕ) (x : ℤ × ℤ) : ℕ :=
  ((Finset.range (k + 1)).filter (fun l => walkPosition X ω l = x)).card

/-- The set of sites visited by the walk up to time k. -/
def visitedSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (k + 1)).image (fun l => walkPosition X ω l)

/-- The maximum local time at time k:
    max_y f_k(y), the maximum number of visits to any single site. -/
def maxLocalTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (k : ℕ) : ℕ :=
  (visitedSites X ω k).sup (localTime X ω k)

/-- The set of favourite sites at time k:
    F(k) = {x ∈ visited sites : f_k(x) = max_y f_k(y)}. -/
def favouriteSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (k : ℕ) : Finset (ℤ × ℤ) :=
  (visitedSites X ω k).filter (fun x => localTime X ω k x = maxLocalTime X ω k)

/-- The cumulative set of favourite sites up to time n:
    ⋃_{k ≤ n} F(k), the set of all sites that were ever a favourite site. -/
def cumulativeFavouriteSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (n + 1)).biUnion (fun k => favouriteSites X ω k)

/--
Erdős Problem #1166 (Erdős–Révész) [Va99, 6.78]:

Given a random walk s₀, s₁, … in ℤ², starting at the origin, let f_k(x) count the
number of 0 ≤ l ≤ k such that s_l = x. Let F(k) = {x : f_k(x) = max_y f_k(y)} be
the set of 'favourite sites'. Is it true that
  |⋃_{k ≤ n} F(k)| ≤ (log n)^{O(1)}
almost surely, for all but finitely many n?

This is true: almost surely |⋃_{k ≤ n} F(k)| ≪ (log n)², which follows from the
fact that almost surely |F(n)| ≤ 3 for all large n (see [1165]) and the result of
Erdős and Taylor [ErTa60] that the maximum number of visits to any fixed point
by time n is ≪ (log n)².

Tags: probability
-/
theorem erdos_problem_1166
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hStep : ∀ i, IsUniformStep μ (X i))
    (hIndep : iIndepFun X μ) :
    ∃ C : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ (n : ℕ) in atTop,
      ((cumulativeFavouriteSites X ω n).card : ℝ) ≤ Real.log (n : ℝ) ^ C :=
  sorry

end Erdos1166
