import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

noncomputable section

/-!
# Erdős Problem #1165

Given a random walk s₀, s₁, … in ℤ², starting at the origin, let f_n(x) count
the number of 0 ≤ k ≤ n such that s_k = x. Let
  F(n) = {x : f_n(x) = max_y f_n(y)}
be the set of 'favourite values'. Find
  ℙ(|F(n)| = r infinitely often)
for r ≥ 3.

A problem of Erdős and Révész [Va99, 6.77]. Status on erdosproblems.com:
SOLVED ("This has been resolved in some other way than a proof or disproof";
page edition 27 January 2026, accessed 2026-02-23; the teorth/erdosproblems
metadata mirror confirms `solved`, last update 2026-01-23, unformalized).
Tóth [To01] proved that this probability is 0 for all r ≥ 4. Hao, Li, Okada,
and Zheng [HLOZ24] proved that this probability is 1 for r = 3.

**Interpretation notes (reviewer, Fable pipeline):**

1. "Random walk" is read as the *simple* random walk on ℤ² (iid uniform
   nearest-neighbour steps), as in the solving papers — both [To01] and
   [HLOZ24] are titled about the *simple* random walk; the page does not
   spell this out.

2. The measurability hypothesis `hMeas` was added by the review: without
   `∀ i, Measurable (X i)`, the hypotheses `IsUniformStep` + `iIndepFun`
   admit a degenerate model — the path space D^ℕ (D the four steps) with the
   *trivial* σ-algebra and its unique probability measure, X i ω = ω i — in
   which every nonempty set has outer measure 1, both hypotheses hold, and
   both conclusions fail: the always-right path has |F(n)| = n + 1 (never 3
   for n ≥ 3), and the path cycling around the unit square has |F(n)| = 4
   infinitely often. With `hMeas`, the four step events partition Ω
   measurably and `IsUniformStep` pins each direction's probability to 1/4.

3. The page attributes the r ≥ 4 case of this ℤ² problem to Tóth [To01],
   whose paper is stated for the one-dimensional simple random walk; the
   two-and-higher-dimensional statements are the subject of [HLOZ24]. The
   page's remark is recorded verbatim above; this attribution nuance is
   noted without altering it.

4. The site's max_y ranges over all y ∈ ℤ², while `maxLocalTime` takes the
   sup over visited sites only; the two agree because the maximum is ≥ 1
   (the origin is visited at k = 0) and unvisited sites have f_n = 0. For
   the same reason, restricting `favouriteSites` to visited sites is exact.

References (stubs; recovered from the archived pipeline logs — the
/latex/1165 extraction and the upstream formal-conjectures fix session — not
independently verified against the live bibliography):

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999, §6.77.

[To01] Tóth, B., _No more than three favorite sites for simple random walk_.
Ann. Probab. 29 (2001), 484–503. (Volume 29 from reviewer knowledge; the
recovered /latex extraction carries journal, year, and pages only.)

[HLOZ24] Hao, C., Li, X., Okada, I. and Zheng, Y., _Favorite sites for
simple random walk in two and more dimensions_. arXiv:2409.00995 (2024).

Tags: probability
-/

namespace Erdos1165

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A step distribution for a simple random walk on ℤ²: the random variable takes
    values in {(1,0), (-1,0), (0,1), (0,-1)} each with equal probability.

    Note: together with `IsProbabilityMeasure μ` and measurability of `X`
    (hypothesis `hMeas` of the theorem below), the four equalities force each
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

/-- The local time (visit count) at site x up to time n:
    f_n(x) = |{k : 0 ≤ k ≤ n | S_k = x}|. -/
def localTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) (x : ℤ × ℤ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => walkPosition X ω k = x)).card

/-- The set of sites visited by the walk up to time n. -/
def visitedSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (n + 1)).image (fun k => walkPosition X ω k)

/-- The maximum local time at time n:
    max_y f_n(y), the maximum number of visits to any single site.

    Taking the sup over `visitedSites` (never empty: it contains S₀) agrees
    with the sup over all of ℤ²: the maximum is ≥ 1 while every unvisited
    site has local time 0. -/
def maxLocalTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : ℕ :=
  (visitedSites X ω n).sup (localTime X ω n)

/-- The set of favourite sites at time n:
    F(n) = {x ∈ visited sites : f_n(x) = max_y f_n(y)}.

    Restricting to visited sites is exact: any x attaining the maximum
    (which is ≥ 1) must have been visited. -/
def favouriteSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : Finset (ℤ × ℤ) :=
  (visitedSites X ω n).filter (fun x => localTime X ω n x = maxLocalTime X ω n)

/--
Erdős Problem #1165 (Erdős–Révész) [Va99, 6.77]:

Given a random walk s₀, s₁, … in ℤ², starting at the origin, let f_n(x) count the
number of 0 ≤ k ≤ n such that s_k = x. Let F(n) = {x : f_n(x) = max_y f_n(y)} be
the set of 'favourite sites'. Find ℙ(|F(n)| = r infinitely often) for r ≥ 3.

Tóth [To01] proved that ℙ(|F(n)| = r i.o.) = 0 for all r ≥ 4.
Hao, Li, Okada, and Zheng [HLOZ24] proved that ℙ(|F(n)| = 3 i.o.) = 1.

The two parts below assert exactly this resolution: ℙ(E) = 1 is encoded as
"E almost surely" and ℙ(E) = 0 as "not-E almost surely" (equivalent for the
measurable i.o. events arising here, given `hMeas`).

**Fix not compile-verified** (this pipeline has no Lean toolchain): the
measurability hypothesis `hMeas` was added by the review — without it the
statement is falsified by a degenerate non-measurable model (see the module
docstring, interpretation note 2); `lake build` must confirm before
downstream use.

Tags: probability
-/
theorem erdos_problem_1165
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hMeas : ∀ i, Measurable (X i))
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
