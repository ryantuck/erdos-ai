import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

noncomputable section

namespace Erdos1165

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

/-- The local time (visit count) at site x up to time n:
    f_n(x) = |{k : 0 ≤ k ≤ n | S_k = x}|. -/
def localTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) (x : ℤ × ℤ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => walkPosition X ω k = x)).card

/-- The set of sites visited by the walk up to time n. -/
def visitedSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (n + 1)).image (fun k => walkPosition X ω k)

/-- The maximum local time at time n:
    max_y f_n(y), the maximum number of visits to any single site. -/
def maxLocalTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : ℕ :=
  (visitedSites X ω n).sup (localTime X ω n)

/-- The set of favourite sites at time n:
    F(n) = {x ∈ visited sites : f_n(x) = max_y f_n(y)}. -/
def favouriteSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : Finset (ℤ × ℤ) :=
  (visitedSites X ω n).filter (fun x => localTime X ω n x = maxLocalTime X ω n)

/--
Erdős Problem #1165 (Erdős–Révész) [Va99, 6.77]:

Given a random walk s₀, s₁, … in ℤ², starting at the origin, let f_n(x) count the
number of 0 ≤ k ≤ n such that s_k = x. Let F(n) = {x : f_n(x) = max_y f_n(y)} be
the set of 'favourite sites'. Find ℙ(|F(n)| = r infinitely often) for r ≥ 3.

Tóth [To01] proved that ℙ(|F(n)| = r i.o.) = 0 for all r ≥ 4.
Hao, Li, Okada, and Zheng [HLOZ24] proved that ℙ(|F(n)| = 3 i.o.) = 1.

Tags: probability
-/
theorem erdos_problem_1165
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hStep : ∀ i, IsUniformStep μ (X i))
    (hIndep : iIndepFun X μ) :
    -- Part 1: |F(n)| = 3 infinitely often, almost surely
    (∀ᵐ ω ∂μ, ∃ᶠ (n : ℕ) in atTop,
      (favouriteSites X ω n).card = 3) ∧
    -- Part 2: |F(n)| = r for r ≥ 4 happens only finitely often, almost surely
    (∀ r : ℕ, r ≥ 4 →
      ∀ᵐ ω ∂μ, ¬∃ᶠ (n : ℕ) in atTop,
        (favouriteSites X ω n).card = r) :=
  sorry

end Erdos1165
