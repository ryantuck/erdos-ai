import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

noncomputable section

/-!
# Erdős Problem #1164

Let R_n be the maximal integer such that almost every random walk from the
origin in ℤ² visits every x ∈ ℤ² with ‖x‖ ≤ R_n in at most n steps.
Is it true that log R_n ≍ √(log n)?

A problem of Erdős and Taylor [Va99, 6.76]. Status on erdosproblems.com:
PROVED ("This has been solved in the affirmative"; page edition 25 January
2026, accessed 2026-02-23; the teorth/erdosproblems metadata mirror confirms
`proved`, last update 2026-01-23, unformalized). Proved independently by
Révész [Re90] and Kesten.

**Interpretation notes (reviewer, Fable pipeline):**

1. Read literally, the page's definition of R_n ("the maximal integer such
   that *almost every* random walk visits every ‖x‖ ≤ R_n in at most n
   steps") is degenerate: for every finite n the walk fails to visit (-1, 0)
   with probability ≥ 4⁻ⁿ > 0, so the largest almost-surely covered radius is
   0 for all n. The standard reading (Révész's book) — used here, as in the
   first-pass file — takes R_n = R_n(ω) to be the random covering radius of
   the individual walk path.

2. The relation log R_n ≍ √(log n) must be read as a two-sided bound **in
   probability** (tightness of both (log R_n)/√(log n) and its reciprocal).
   The almost-sure version with fixed constants — "∃ c₁, c₂ > 0 such that
   a.s. eventually c₁√(log n) ≤ log R_n ≤ c₂√(log n)", which is what the
   first-pass file asserted — is **false**: by [DPRZ04] the ratio
   V_n = (log R_n)²/log n has a nondegenerate limit law with full support on
   (0, ∞), so P(V_n < c₁²) and P(V_n > c₂²) tend to positive limits for any
   fixed c₁, c₂ > 0, and (with a zero-one law) liminf V_n = 0 and
   limsup V_n = ∞ almost surely.

3. The stronger Révész–Kesten conjecture is printed on the page as
   lim_{n→∞} P((log R_n)²/log n ≤ x) = e^{-4x} for all x > 0. As written
   this is impossible (the left side is nondecreasing in x, the right side
   strictly decreasing), so the page formula is a transcription slip. The
   corrected form, proved by Dembo, Peres, Rosen, and Zeitouni [DPRZ04], is
   lim_{n→∞} P((log R_n)²/log n ≤ x) = e^{-4/x}, i.e. (log R_n)²/log n
   converges in law to 4/E with E exponential of rate 1 (equivalently
   (log n)/(log R_n)² ⇒ Exp(4)). The variant below formalizes the corrected
   form.

References (stubs; recovered from the archived pipeline logs — the /latex/1164
extraction and the upstream formal-conjectures fix session — not independently
verified against the live bibliography):

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999, §6.76.

[Re90] Révész, P., _Random walk in random and nonrandom environments_,
World Scientific, 1990, xiv+332 pp.

[DPRZ04] Dembo, A., Peres, Y., Rosen, J. and Zeitouni, O., _Cover times for
Brownian motion and random walks in two dimensions_, Annals of Mathematics (2)
160 (2004), 433–464. (Volume 160 from the prior review and reviewer knowledge;
the recovered /latex extraction carries journal, year, and pages only.)

Tags: probability
-/

namespace Erdos1164

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

/-- The covering radius R_n(ω): the largest R ∈ ℕ such that every lattice point
    (a, b) ∈ ℤ² with a² + b² ≤ R² is visited by the walk within its first n steps
    (positions S₀, …, S_n).

    The defining set always contains R = 0 (S₀ = (0,0) covers the only point of
    the closed disk of radius 0) and is bounded above (the walk visits at most
    n + 1 distinct points, while the disk of radius R contains at least 2R + 1
    lattice points), so `sSup` is a genuine maximum. -/
noncomputable def coveringRadius (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : ℕ :=
  sSup {R : ℕ | ∀ (a b : ℤ), a ^ 2 + b ^ 2 ≤ ↑R ^ 2 →
    ∃ k, k ≤ n ∧ walkPosition X ω k = (a, b)}

/--
Erdős Problem #1164 (Erdős–Taylor) [Va99, 6.76]:

Let R_n be the maximal integer such that almost every random walk from the origin
in ℤ² visits every x ∈ ℤ² with ‖x‖ ≤ R_n in at most n steps. Is it true that
  log R_n ≍ √(log n)?

This is true, as proved independently by Révész [Re90] and Kesten, in the
**in-probability** sense formalized here: for every ε > 0 there are constants
c₁, c₂ > 0 such that for all sufficiently large n,
  P(c₁ · √(log n) ≤ log R_n ≤ c₂ · √(log n)) ≥ 1 - ε.

(The first-pass encoding — almost surely, eventually, with fixed constants —
is false: the limit law of [DPRZ04] (see the variant below) gives the ratio
(log R_n)²/log n full support on (0, ∞) in the limit, so no fixed constants
can work almost surely. See the module docstring, interpretation note 2.)

**Fix not compile-verified** (this pipeline has no Lean toolchain): the
measurability hypothesis `hMeas` was added and the conclusion recast from the
false a.s. form; `lake build` must confirm before downstream use.

Tags: probability
-/
theorem erdos_problem_1164
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hMeas : ∀ i, Measurable (X i))
    (hStep : ∀ i, IsUniformStep μ (X i))
    (hIndep : iIndepFun X μ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ᶠ (n : ℕ) in atTop,
          1 - ε ≤ (μ {ω |
            c₁ * Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (coveringRadius X ω n : ℝ) ∧
            Real.log (coveringRadius X ω n : ℝ) ≤ c₂ * Real.sqrt (Real.log (n : ℝ))}).toReal :=
  sorry

/--
The stronger Révész–Kesten conjecture, proved by Dembo, Peres, Rosen, and
Zeitouni [DPRZ04]: for every x > 0,
  lim_{n→∞} P((log R_n)² / log n ≤ x) = e^{-4/x}.

The problem page prints the right-hand side as e^{-4x}, which cannot be the
limit of the (nondecreasing-in-x) left-hand side; e^{-4/x} is the corrected
form (see the module docstring, interpretation note 3). Division junk values
((log R_n)²/log n = 0 when n ≤ 1, since `Real.log` division by 0 yields 0) are
harmless under `atTop`.

**New statement, not compile-verified.**
-/
theorem erdos_problem_1164.variants.dembo_peres_rosen_zeitouni
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hMeas : ∀ i, Measurable (X i))
    (hStep : ∀ i, IsUniformStep μ (X i))
    (hIndep : iIndepFun X μ) :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ =>
          (μ {ω | Real.log (coveringRadius X ω n : ℝ) ^ 2 / Real.log (n : ℝ) ≤ x}).toReal)
        atTop (nhds (Real.exp (-4 / x))) :=
  sorry

end Erdos1164
