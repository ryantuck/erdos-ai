import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Erdős Problem #1147

Let α > 0 be an irrational number. Is the set A = { n ≥ 1 : ‖αn²‖ < 1/log n },
where ‖·‖ denotes the distance to the nearest integer, an additive basis of
order 2?

Verbatim source statement (erdosproblems.com/1147): "Let $\alpha>0$ be an
irrational number. Is the set \[A=\left\{ n\geq 1: \| \alpha n^2\| <
\frac{1}{\log n}\right\},\] where $\|\cdot\|$ denotes the distance to the
nearest integer, an additive basis of order $2$?"

Status: DISPROVED per erdosproblems.com/1147 (page last edited 27 January
2026, accessed 2026-02-23) — "This has been solved in the negative."

Remarks from the source page:
* "This was disproved by Konieczny [Ko16b], and is false both for almost every
  $\alpha>0$, and also is false specifically for $\alpha=\sqrt{2}$."
* "More generally, given any $\epsilon(n)\to 0$, the set
  $A=\{ n\geq 1: \|\alpha n^2\| < \epsilon(n)\}$ is not an additive basis of
  order $2$ for almost every $\alpha>0$."

The main theorem states the concrete refutation witness (α = √2); the variants
record the refuted-universal reading of the question and the two
almost-everywhere results quoted above. Tags: irrational, additive basis.
Additional thanks (site): Quanyu Tang. No OEIS entries or cross-references are
listed on the page.

References (honest stubs; full records DEFERRED — see fable-review/1147.md):

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.21. (Corpus-canonical identity of this key, per the upstream
  contributing guide. The styled archive's and prior review's gloss of [Va99]
  as Vaughan, _The Hardy-Littlewood method_, 2nd ed. (1997) is a hallucinated
  attribution — the erdosproblems.com page carries only the bare key
  [Va99,1.21] — and is deliberately not reproduced here.)

[Ko16b] Konieczny, J., _Sets of recurrence as bases for the positive
  integers_. Acta Arithmetica (2016), 309–338. (Title, journal and pages from
  the original pipeline's fetch of erdosproblems.com/latex/1147; the volume
  number is absent there and has not been invented.)
-/

noncomputable section

namespace Erdos1147

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- The set A(α) = { n ≥ 1 : ‖αn²‖ < 1/log n }.

Boundary note: at n = 1 we have `Real.log 1 = 0`, and Lean's division
convention gives `1 / 0 = 0`, so the (nonnegative) distance is never `< 0`
and `1 ∉ setA α` for every α — whereas the source's condition "‖α‖ < 1/log 1"
is undefined. This is harmless for the *negative* main statement below:
`IsAdditiveBasisOrder2` is monotone under `⊆`, so failure of the basis
property for `setA α ∪ {1}` implies failure for `setA α`. (It is not harmless
in general — a single element can turn a non-basis into a basis, e.g. the
even numbers versus the even numbers together with 1.) -/
def setA (α : ℝ) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ distNearestInt (α * (↑n) ^ 2) < 1 / Real.log (↑n)}

/-- The generalized set A(α, ε) = { n ≥ 1 : ‖αn²‖ < ε(n) } for an arbitrary
    threshold function ε : ℕ → ℝ, as in the source page's final remark. -/
def setAGen (α : ℝ) (ε : ℕ → ℝ) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ distNearestInt (α * (↑n) ^ 2) < ε n}

/-- A set S ⊆ ℕ is an additive basis of order 2 if every sufficiently large
    natural number can be written as a sum of two elements from S. -/
def IsAdditiveBasisOrder2 (S : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → ∃ a ∈ S, ∃ b ∈ S, n = a + b

/--
Erdős Problem #1147 [Va99, 1.21] (Disproved):

Let α > 0 be an irrational number. Is the set
  A = { n ≥ 1 : ‖αn²‖ < 1/log n },
where ‖·‖ denotes the distance to the nearest integer, an additive basis
of order 2?

This was disproved by Konieczny [Ko16b]. In particular, for α = √2,
the set A is not an additive basis of order 2 — the statement formalized
here; since √2 is a positive irrational, it refutes the universally
quantified question (see `erdos_problem_1147.variants.not_forall`).

More generally, for any ε(n) → 0, the set { n ≥ 1 : ‖αn²‖ < ε(n) }
is not an additive basis of order 2 for almost every α > 0.

Tags: irrational, additive basis
-/
theorem erdos_problem_1147 :
    ¬ IsAdditiveBasisOrder2 (setA (Real.sqrt 2)) :=
  sorry

/-- The refuted-universal reading of the question [Ko16b]: it is *not* the
case that for every irrational α > 0 the set A(α) is an additive basis of
order 2. Implied by `erdos_problem_1147` (√2 is a positive irrational);
logically equivalent to the upstream styled encoding
`answer(False) ↔ ∀ α, Irrational α → α > 0 → …`. -/
theorem erdos_problem_1147.variants.not_forall :
    ¬ ∀ α : ℝ, Irrational α → α > 0 → IsAdditiveBasisOrder2 (setA α) :=
  sorry

/-- [Ko16b]: the original question's set A(α) fails to be an additive basis
of order 2 for almost every α > 0 (Lebesgue measure) — the page's "false
for almost every α > 0". -/
theorem erdos_problem_1147.variants.almost_all :
    ∀ᵐ α : ℝ ∂MeasureTheory.volume,
      α > 0 → ¬ IsAdditiveBasisOrder2 (setA α) :=
  sorry

/-- [Ko16b]: more generally, given any ε(n) → 0, the set
{ n ≥ 1 : ‖αn²‖ < ε(n) } is not an additive basis of order 2 for almost
every α > 0. -/
theorem erdos_problem_1147.variants.general_threshold (ε : ℕ → ℝ)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    ∀ᵐ α : ℝ ∂MeasureTheory.volume,
      α > 0 → ¬ IsAdditiveBasisOrder2 (setAGen α ε) :=
  sorry

end Erdos1147
