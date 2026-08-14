import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Filter Polynomial MeasureTheory Set

noncomputable section

namespace Erdos1152

/-!
# Erdős Problem #1152

For n ≥ 1 fix some sequence of n distinct numbers x₁ₙ, ..., xₙₙ ∈ [-1,1].
Let ε = ε(n) → 0. Does there always exist a continuous function
f : [-1,1] → ℝ such that if pₙ is a sequence of polynomials, with degrees
deg pₙ < (1 + ε(n))n, such that pₙ(xₖₙ) = f(xₖₙ) for all 1 ≤ k ≤ n, then
pₙ(x) ↛ f(x) for almost all x ∈ [-1,1]?

Verbatim source statement (erdosproblems.com/1152): "For $n\geq 1$ fix some
sequence of $n$ distinct numbers $x_{1n},\ldots,x_{nn}\in [-1,1]$. Let
$\epsilon=\epsilon(n)\to 0$. Does there always exist a continuous function
$f:[-1,1]\to \mathbb{R}$ such that if $p_n$ is a sequence of polynomials,
with degrees $\deg p_n<(1+\epsilon(n))n$, such that $p_n(x_{kn})=f(x_{kn})$
for all $1\leq k\leq n$, then $p_n(x)\not\to f(x)$ for almost all
$x\in [-1,1]$?"

Status: OPEN per erdosproblems.com/1152 (page last edited 23 January 2026,
accessed 2026-02-23) — "This is open, and cannot be resolved with a finite
computation." Source line: #1152: [Va99, 2.42].

Remark from the source page: Erdős, Kroó, and Szabados [EKS89] proved that,
if ε > 0 is fixed and does not → 0, then there exist sequences xᵢⱼ such
that, for any continuous function f, there exists a sequence of polynomials
pₙ, with degrees deg pₙ < (1+ε)n, such that pₙ(xₖₙ) = f(xₖₙ) for all
1 ≤ k ≤ n, and pₙ(x) → f(x) uniformly for all x ∈ [-1,1]. (Formalized
below as `erdos_problem_1152.variants.eks89_fixed_epsilon`.)

Encoding notes:

* The source poses a yes/no question and the problem is OPEN; this raw
  corpus has no `answer()` elaborator (Mathlib-only imports), and its
  uniform convention for open yes/no questions is a direct assertion of the
  asked ("yes") direction with a `sorry` proof, as here. In styled question
  form it would be `answer(sorry) ↔ ∀ x …` (the upstream formal-conjectures
  file for this problem, recovered from the session logs, uses exactly that
  shape over this same proposition).
* The `n ≥ 1` guard on the degree hypothesis is essential, not cosmetic:
  without it the n = 0 instance would demand `((p 0).natDegree : ℝ) < 0`,
  which no polynomial satisfies, so the ∀p quantifier would be vacuous and
  the whole theorem trivially true.
* The positivity hypothesis `0 < ε n` is not in the source text ("Let
  ε = ε(n) → 0" carries no sign), but positivity is the intended regime —
  the page's contrast is with *fixed* ε > 0 [EKS89] — and the restriction
  loses no content: for ε(n) ∈ (-1/n, 0] the degree bound < (1+ε(n))n pins
  pₙ to the unique Lagrange interpolant (degree ≤ n-1), the regime of the
  Erdős–Vértesi a.e.-divergence theorem (Acta Math. Acad. Sci. Hungar.,
  1980 — reviewer knowledge, not page content), and if ε(n) ≤ -1/n for some
  n one can choose f whose level-n values lie on no polynomial of the
  permitted degree, so no admissible p exists and that instance is
  trivially satisfied.
* Non-vacuity: for every continuous f, node array, and ε with ε(n) > 0, the
  Lagrange interpolants Lₙ (natDegree ≤ n-1 < n < (1+ε(n))n, together with
  p 0 := 0) satisfy both hypotheses, so the ∀p quantifier always has
  witnesses and the a.e.-divergence demand is substantive.
* `natDegree` on the zero polynomial is 0, which the bound admits for all
  n ≥ 1 — consistent with the deg 0 = -∞ convention; harmless either way.

Tags (per the page): analysis, polynomials.
Formalised statement (per the page, as of access): No.
The page records 0 forum comments and no related OEIS sequences.

References (honest stubs; no `/latex/1152` or `/bibs/` fetch was captured in
the session logs, so entries carry only page- or corpus-corroborated data —
nothing fabricated):

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §2.42. (Corpus-canonical identity of this site-global key, settled by the
  log-recovered `/latex/1005` and `/latex/1151` extractions and by sibling
  reviews 1068 and 1131–1151; the neighbouring interpolation problems 1132
  and 1153 cite §2.43 and §2.44 of the same booklet. The archived styled
  copy of this problem glossed [Va99] as "Vértesi, P., _Classical
  (unweighted) and weighted interpolation_ (1999)" — a hallucinated
  attribution, not reproduced here.)

[EKS89] Erdős, P., Kroó, A., and Szabados, J., _On convergent interpolatory
  polynomials_ (1989). (Authors from the page prose and year from the key;
  the title is corroborated by reviewer knowledge, which places the paper in
  J. Approx. Theory 58 (1989), 232–241 — journal/volume/pages unverified
  against the site and therefore left out of the stub proper.)
-/

/--
Erdős Problem #1152 [Va99, 2.42] (Open):

For n ≥ 1 fix some sequence of n distinct numbers x₁ₙ, ..., xₙₙ ∈ [-1,1],
and let ε = ε(n) → 0 with ε(n) > 0. Does there always exist a continuous
function f : [-1,1] → ℝ such that every sequence of polynomials pₙ with
deg pₙ < (1 + ε(n))n interpolating f at the nodes fails to converge to f
at almost every x ∈ [-1,1]?

This theorem asserts the "yes" direction of the open question, per this
corpus's convention for open yes/no questions (in styled question form it
would be `answer(sorry) ↔ …`): for any triangular array of distinct
interpolation nodes in [-1,1] and any positive function ε(n) → 0, there
exists a continuous function f : [-1,1] → ℝ such that every sequence of
polynomials pₙ with deg pₙ < (1 + ε(n))n interpolating f at the nodes
fails to converge to f for almost every x ∈ [-1,1].

Tags: analysis, polynomials
-/
theorem erdos_problem_1152
    (x : (n : ℕ) → Fin n → ℝ)
    (hx_range : ∀ n, ∀ k : Fin n, x n k ∈ Icc (-1 : ℝ) 1)
    (hx_distinct : ∀ n, Function.Injective (x n))
    (ε : ℕ → ℝ)
    (hε_pos : ∀ n, 0 < ε n)
    (hε_lim : Tendsto ε atTop (nhds 0)) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) ∧
      ∀ p : ℕ → Polynomial ℝ,
        (∀ n, n ≥ 1 → ((p n).natDegree : ℝ) < (1 + ε n) * n) →
        (∀ n, ∀ k : Fin n, (p n).eval (x n k) = f (x n k)) →
        ∀ᵐ t ∂(volume.restrict (Icc (-1 : ℝ) 1)),
          ¬Tendsto (fun n => (p n).eval t) atTop (nhds (f t)) :=
  sorry

/--
The page's remark, proved by Erdős, Kroó, and Szabados [EKS89]: if ε > 0 is
fixed (and does not → 0), then there exist sequences xᵢⱼ such that, for any
continuous function f, there exists a sequence of polynomials pₙ with
deg pₙ < (1+ε)n, such that pₙ(xₖₙ) = f(xₖₙ) for all 1 ≤ k ≤ n, and
pₙ(x) → f(x) uniformly for all x ∈ [-1,1].

Encoding notes: the witness node array is required to lie in [-1,1] with
distinct nodes at each level, matching the setup of the main problem (the
remark's "sequences xᵢⱼ" are interpolation node systems of the same kind);
the degree bound carries the same essential `n ≥ 1` guard as the main
theorem; and uniform convergence on [-1,1] is spelled out in ε–N form using
only constructs available from this file's imports.
-/
theorem erdos_problem_1152.variants.eks89_fixed_epsilon
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : (n : ℕ) → Fin n → ℝ,
      (∀ n, ∀ k : Fin n, x n k ∈ Icc (-1 : ℝ) 1) ∧
      (∀ n, Function.Injective (x n)) ∧
      ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) →
        ∃ p : ℕ → Polynomial ℝ,
          (∀ n, n ≥ 1 → ((p n).natDegree : ℝ) < (1 + ε) * n) ∧
          (∀ n, ∀ k : Fin n, (p n).eval (x n k) = f (x n k)) ∧
          ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n, N ≤ n →
            ∀ t ∈ Icc (-1 : ℝ) 1, |(p n).eval t - f t| < δ :=
  sorry

end Erdos1152
