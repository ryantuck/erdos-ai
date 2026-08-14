import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #1144

Let $f$ be a random completely multiplicative function, where for each prime
$p$ we independently choose $f(p) \in \{-1, 1\}$ uniformly at random. Is it
true that
$$\limsup_{N\to\infty} \frac{\sum_{m\leq N} f(m)}{\sqrt{N}} = \infty$$
with probability $1$?

Verbatim source statement (erdosproblems.com/1144): "Let $f$ be a random
completely multiplicative function, where for each prime $p$ we independently
choose $f(p)\in \{-1,1\}$ uniformly at random. Is it true that
\[\limsup_{N\to \infty}\frac{\sum_{m\leq N}f(m)}{\sqrt{N}}=\infty\]
with probability $1$?"

Status: OPEN per erdosproblems.com/1144 (page last edited 26 January 2026,
accessed 2026-02-23) — "This is open, and cannot be resolved with a finite
computation."

Remarks from the source page:
* "This model of a random multiplicative function is sometimes called a
  Rademacher function, although this is sometimes reserved for a merely
  multiplicative function (which is $0$ on non-squarefree integers). See
  [520] for the partial sums of this alternative model." (Cross-reference:
  Erdős problem #520.)
* "It should also be compared to another popular model of random completely
  multiplicative functions, Steinhaus functions, which have $f(p)$ uniformly
  distributed over the unit circle." (Context only — the page states no
  specific Steinhaus claim, so no Steinhaus variant is formalized here.)
* "Atherfold [At25] has proved that, almost surely,
  \[\sum_{m\leq N}f(m)\ll N^{1/2}(\log N)^{1+o(1)}.\]" (Formalized below as
  `erdos_problem_1144.variants.atherfold_upper`.)

Additional thanks to (per the page): Adam Harper.
Tags: number theory, probability
Formalised statement (per the page, as of access): No.

Reference: [Va99, 1.11]
https://www.erdosproblems.com/1144

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.11. (Honest stub; the site's `/latex/1144` extraction recovered from the
  session logs carries no [Va99] details, and this identification follows the
  site's uniform bibliography for the key — corroborated by sibling problems
  1068 and 1137–1143 and by upstream formal-conjectures files captured in the
  logs. Note: the glosses of `[Va99]` as "Vaughan, R.C., _Multiplicative
  Number Theory I: Classical Theory_, 1999" (upstream first pass) and as
  "Montgomery, H.L. and Vaughan, R.C., _Multiplicative Number Theory I_,
  2007" (prior ai-review, propagated into the styled upstream file) are both
  hallucinations for this key.)
[At25] Atherfold, C., _Almost sure bounds for weighted sums of Rademacher
  random multiplicative functions_. arXiv:2501.11076 (2025). (Per the
  `/latex/1144` extraction recovered from the session logs.)
-/

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

noncomputable section

namespace Erdos1144

/-- A random variable is Rademacher distributed: takes values ±1 with equal
probability. (For a *measurable* `X` on a probability space the two
complementary sets each get measure 1/2; measurability is required separately
at the use sites, since without it `μ` is only an outer measure on these sets
and the equality does not pin down the distribution.) -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/-- The random completely multiplicative function built from Rademacher signs at primes.
    For n ≥ 1: f(n) = ∏_{p ∈ primeFactors(n)} ε(p)^{v_p(n)}.
    For n = 0: f(0) = 0. -/
noncomputable def randMultFun {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else ∏ p ∈ n.factorization.support, (ε p ω) ^ (n.factorization p)

/-- The partial sum ∑_{m=1}^{N} f(m). -/
noncomputable def partialSum {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, randMultFun ε ω m

/--
Erdős Problem #1144 [Va99, 1.11] (Open):

Let f be a random completely multiplicative function, where for each prime p
we independently choose f(p) ∈ {-1, 1} uniformly at random. Is it true that
  limsup_{N → ∞} (∑_{m ≤ N} f(m)) / √N = ∞
with probability 1?

This model is sometimes called a Rademacher random multiplicative function
(a name sometimes reserved for the merely multiplicative model that vanishes
on non-squarefree integers — see Erdős problem #520 for that model's partial
sums; compare also the Steinhaus model, with f(p) uniform on the unit circle).
Atherfold [At25] proved that, almost surely,
  ∑_{m ≤ N} f(m) ≪ N^{1/2} (log N)^{1+o(1)}
(see `erdos_problem_1144.variants.atherfold_upper`).

Encoding notes:
* The conclusion `∀ᵐ ω, ∀ C, ∃ᶠ N in atTop, S_N(ω) > C·√N` is exactly
  "with probability 1, limsup_{N→∞} S_N/√N = ∞": for N ≥ 1 one has
  S_N > C√N ↔ S_N/√N > C, and N = 0 (where both sides degenerate) is
  invisible to `∃ᶠ _ in atTop`. The a.e. quantifier is (correctly) outermost.
* `hMeas` (measurability of each sign) is essential, not a formality:
  Mathlib's `iIndepFun` places no measurability requirement on the family
  (it is independence of the comap σ-algebras), and `μ` applied to the
  non-measurable sets `{ε k = ±1}` is only an outer measure, so `hRad` alone
  does not force the masses to be 1/2. Without `hMeas` the statement is
  refutable outright: on [0,1] × {±1}^ℕ one can build (by a Bernstein-set
  transfinite induction, using choice) a family satisfying `hRad` and
  `hIndep` verbatim — all the relevant non-measurable sets and their finite
  intersections have outer measure 1, making every independence product
  1 = 1·…·1 — yet whose sign pattern on a set of full outer measure equals
  the fixed deterministic completely multiplicative function given by
  f(p) = χ₃(p) for p ≠ 3, f(3) = 1, whose partial sums are O(log N) = o(√N).
  With `hMeas`, the hypotheses pin the joint law to the canonical product of
  uniform ±1 marginals and the statement is the intended one.
* The hypotheses are imposed at all indices k ∈ ℕ although `randMultFun`
  only reads ε at primes; this is an equivalent packaging (a prime-indexed
  independent Rademacher family extends to all of ℕ on a product space, and
  the conclusion transfers back by Fubini).

Tags: number theory, probability
-/
theorem erdos_problem_1144
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℕ → Ω → ℝ}
    (hMeas : ∀ k, Measurable (ε k))
    (hRad : ∀ k, IsRademacher μ (ε k))
    (hIndep : iIndepFun ε μ) :
    ∀ᵐ ω ∂μ, ∀ C : ℝ,
      ∃ᶠ N in atTop,
        partialSum ε ω N > C * Real.sqrt (N : ℝ) :=
  sorry

/--
Variant (solved): Atherfold [At25] proved that, almost surely,
  ∑_{m ≤ N} f(m) ≪ N^{1/2} (log N)^{1+o(1)},
rendered here as: almost surely, for every δ > 0, eventually
  |S_N| ≤ √N · (log N)^{1+δ}.
(For any fixed δ the implied constant of `≪` is absorbed eventually since
(log N)^{δ/2} → ∞; small N, where log N ≤ 0 makes the real rpow degenerate,
are invisible to `∀ᶠ _ in atTop`.) Page-confirmed; not compile-verified.
-/
theorem erdos_problem_1144.variants.atherfold_upper
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℕ → Ω → ℝ}
    (hMeas : ∀ k, Measurable (ε k))
    (hRad : ∀ k, IsRademacher μ (ε k))
    (hIndep : iIndepFun ε μ) :
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ N in atTop,
        |partialSum ε ω N| ≤ Real.sqrt (N : ℝ) * (Real.log N) ^ (1 + δ) :=
  sorry

end Erdos1144
