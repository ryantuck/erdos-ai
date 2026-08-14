import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

noncomputable section

/-!
# Erdős Problem #1166

Given a random walk s₀, s₁, … in ℤ², starting at the origin, let f_k(x) count
the number of 0 ≤ l ≤ k such that s_l = x. Let
  F(k) = {x : f_k(x) = max_y f_k(y)}
be the set of 'favourite values' (favourite sites). Is it true that
  |⋃_{k ≤ n} F(k)| ≤ (log n)^{O(1)}
almost surely, for all but finitely many n?

A problem of Erdős and Révész [Va99, 6.78]. Status on erdosproblems.com:
PROVED ("This has been solved in the affirmative"; page edition 23 January
2026, accessed 2026-02-23; the teorth/erdosproblems metadata mirror confirms
`proved`, last update 2026-01-23, unformalized, OEIS "possible"). Per the
page's remarks: this is true — almost surely |⋃_{k ≤ n} F(k)| ≪ (log n)²,
which follows from the fact that almost surely |F(n)| ≤ 3 for all large n
(see [1165]) and the result of Erdős and Taylor [ErTa60] that, if T_n is the
maximum number of visits of a random walk by time n to any fixed point, then
T_n ≪ (log n)².

**Interpretation notes (reviewer, Fable pipeline):**

1. "Random walk in ℤ²" is read, as in the sibling problems 1164 and 1165, as
   the simple random walk: i.i.d. uniform steps on
   {(1,0), (-1,0), (0,1), (0,-1)}.

2. The measurability hypothesis `hMeas` is required: without it, the trivial
   σ-algebra on the path space carries a probability measure under which
   `IsUniformStep` and `iIndepFun` both hold (every nonempty event has outer
   measure 1) while the conclusion fails — the always-right path visits every
   site exactly once, so every visited site is a favourite at every time and
   |⋃_{k ≤ n} F(k)| = n + 1 grows linearly, beating (log n)^C for every C;
   the exceptional set is nonempty, hence of outer measure 1. The first-pass
   file omitted `hMeas`, making the stated theorem false.

3. The exponent C in (log n)^{O(1)} is a deterministic constant, quantified
   outside the almost-sure and eventual quantifiers. This is the standard
   reading of O(1), and the known bound ≪ (log n)² makes any fixed C ≥ 3
   work (an implied multiplicative constant is absorbed into one extra power
   of log n for large n).

References (stubs; recovered from the archived pipeline logs — the page
capture and the upstream formal-conjectures fix session — not independently
verified against the live bibliography):

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999, §6.78.
(The upstream fix session identified this canonical expansion, replacing a
fabricated "Varga, L." attribution in the styled corpus; the raw first-pass
file under review never attributed [Va99].)

[ErTa60] Erdős, P. and Taylor, S. J., _Some problems concerning the structure
of random walk paths_, Acta Math. Acad. Sci. Hungar. 11 (1960), 137–162.

[1165] Erdős Problem #1165 (erdosproblems.com/1165): almost surely
|F(n)| ≤ 3 for all large n (Tóth proved ℙ(|F(n)| = r i.o.) = 0 for r ≥ 4;
Hao, Li, Okada, and Zheng proved ℙ(|F(n)| = 3 i.o.) = 1).

Tags: probability
-/

namespace Erdos1166

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A step distribution for a simple random walk on ℤ²: the random variable takes
    values in {(1,0), (-1,0), (0,1), (0,-1)} each with equal probability.

    Note: together with `IsProbabilityMeasure μ` and measurability of `X`
    (hypothesis `hMeas` of the theorems below), the four equalities force each
    direction to have probability 1/4; without measurability the four events
    need not be μ-measurable and equality of their outer measures does not pin
    down the distribution. -/
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
    max_y f_k(y), the maximum number of visits to any single site.

    `visitedSites X ω k` always contains S₀ = (0,0), so `Finset.sup` is a
    genuine maximum (never the junk default 0 of an empty sup); and since
    unvisited sites have local time 0 < 1 ≤ maxLocalTime, the maximum over
    visited sites equals the maximum over all of ℤ². -/
def maxLocalTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (k : ℕ) : ℕ :=
  (visitedSites X ω k).sup (localTime X ω k)

/-- The set of favourite sites at time k:
    F(k) = {x ∈ visited sites : f_k(x) = max_y f_k(y)}.

    Restricting to visited sites loses nothing: an unvisited site has local
    time 0 and the maximum is ≥ 1 (the origin is visited at time 0). -/
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

**Fix not compile-verified** (this pipeline has no Lean toolchain): the
measurability hypothesis `hMeas` was added — without it a degenerate
non-measurable model falsifies the statement (see the module docstring,
interpretation note 2); `lake build` must confirm before downstream use.

Tags: probability
-/
theorem erdos_problem_1166
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hMeas : ∀ i, Measurable (X i))
    (hStep : ∀ i, IsUniformStep μ (X i))
    (hIndep : iIndepFun X μ) :
    ∃ C : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ (n : ℕ) in atTop,
      ((cumulativeFavouriteSites X ω n).card : ℝ) ≤ Real.log (n : ℝ) ^ C :=
  sorry

/--
The stronger bound recorded in the remarks of erdosproblems.com/1166: almost
surely
  |⋃_{k ≤ n} F(k)| ≪ (log n)²,
i.e. there is a deterministic constant C > 0 such that almost surely, for all
but finitely many n, |⋃_{k ≤ n} F(k)| ≤ C (log n)². (A deterministic constant
suffices: the page derives the bound from the eventual bound |F(n)| ≤ 3 and
the Erdős–Taylor bound T_n ≪ (log n)², whose almost-sure limsup normalization
is a deterministic constant.)

**New statement, not compile-verified.**
-/
theorem erdos_problem_1166.variants.log_squared_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hMeas : ∀ i, Measurable (X i))
    (hStep : ∀ i, IsUniformStep μ (X i))
    (hIndep : iIndepFun X μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂μ, ∀ᶠ (n : ℕ) in atTop,
      ((cumulativeFavouriteSites X ω n).card : ℝ) ≤ C * Real.log (n : ℝ) ^ 2 :=
  sorry

/--
The Erdős–Taylor ingredient quoted in the remarks of erdosproblems.com/1166
[ErTa60]: if T_n is the maximum number of visits of the walk by time n to any
fixed point (here `maxLocalTime`), then almost surely T_n ≪ (log n)², i.e.
there is a deterministic constant C > 0 with T_n ≤ C (log n)² for all but
finitely many n. (Erdős and Taylor proved the almost-sure bounds
1/(4π) ≤ liminf T_n/(log n)² ≤ limsup T_n/(log n)² ≤ 1/π, so a deterministic
C works.)

**New statement, not compile-verified.**
-/
theorem erdos_problem_1166.variants.erdos_taylor_max_visits
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hMeas : ∀ i, Measurable (X i))
    (hStep : ∀ i, IsUniformStep μ (X i))
    (hIndep : iIndepFun X μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂μ, ∀ᶠ (n : ℕ) in atTop,
      ((maxLocalTime X ω n : ℝ)) ≤ C * Real.log (n : ℝ) ^ 2 :=
  sorry

/--
The other ingredient quoted verbatim in the remarks of erdosproblems.com/1166:
"almost surely |F(n)| ≤ 3 for all large n (see [1165])". Formalized exactly as
the page states it; see Problem 1165 (Tóth: ℙ(|F(n)| = r i.o.) = 0 for r ≥ 4;
Hao–Li–Okada–Zheng: ℙ(|F(n)| = 3 i.o.) = 1) for the surrounding results.

**New statement, not compile-verified.**
-/
theorem erdos_problem_1166.variants.favourite_sites_eventually_le_three
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hMeas : ∀ i, Measurable (X i))
    (hStep : ∀ i, IsUniformStep μ (X i))
    (hIndep : iIndepFun X μ) :
    ∀ᵐ ω ∂μ, ∀ᶠ (n : ℕ) in atTop,
      (favouriteSites X ω n).card ≤ 3 :=
  sorry

end Erdos1166
