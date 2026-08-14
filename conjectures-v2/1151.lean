import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

noncomputable section
open Classical Finset BigOperators

namespace Erdos1151

/-!
# Erdős Problem #1151

Verbatim source statement (erdosproblems.com/1151, page edition 23 January
2026, accessed 2026-02-23; status **OPEN** — "This is open, and cannot be
resolved with a finite computation."):

"Given $a_1,\ldots,a_n\in [-1,1]$ let
$\mathcal{L}^nf(x) = \sum_{1\leq i\leq n}f(a_i)\ell_i(x)$ be the unique
polynomial of degree $n-1$ which agrees with $f$ on $a_i$ for $1\leq i\leq n$
(that is, the Lagrange interpolation polynomial).

Let $a_i$ be the set of Chebyshev nodes. Prove that, for any closed
$A\subseteq [-1,1]$, there exists a continuous function $f$ such that $A$ is
the set of limit points of $\mathcal{L}^nf(x)$."

Source line: #1151: [Va99, 2.41]. Tags: analysis | polynomials. No related
OEIS sequences; 0 forum comments; "Formalised statement? No" as of the access
date.

Remarks from the page:

- "This is as the problem is given in [Va99], but I am unclear exactly what is
  intended here - is this meant for fixed, arbitrary, $x\in [-1,1]$?" (the
  variable $x$ is *free* in the displayed statement — the ambiguity is
  acknowledged by the site owner).
- Erdős [Er41] proved that, if $x=\cos(\pi p/q)$ for some odd integers
  $p,q\geq 1$, then there is a continuous function $f$ such that
  $\lim_{n\to \infty}\mathcal{L}^nf(x)=\infty$, where the limit is taken over
  the sequence of Chebyshev nodes as $n\to\infty$. In [Er43] he claims
  (without proof) that for any closed set $A$ there exists a continuous $f$
  such that the limit points of $\mathcal{L}^nf(x)$ is $A$ *(for specific $x$
  of this shape)*.

## Resolution of the $x$-ambiguity (Fable review, 2026-08-14)

The first-pass formalization resolved the free $x$ as "for all
$x \in [-1,1]$". That reading is **provably false**: $0$ is a Chebyshev node
of every odd order $m$ (take $k=(m-1)/2$: $\cos(m\pi/(2m)) = \cos(\pi/2) =
0$), and Lagrange interpolation reproduces $f$ at its nodes, so
$\mathcal{L}^m f(0) = f(0)$ along all odd $m$. Hence $f(0)$ is a limit point
of the sequence for *every* $f$, and the closed set $A = \emptyset \subseteq
[-1,1]$ (realizable at Erdős's points via [Er41] divergence) can never be
realized at $x = 0$. More generally every $x = \cos(\pi a/b)$ with $b$ even
(in lowest terms) is a Chebyshev node for infinitely many orders and admits
the same obstruction. See `erdos_problem_1151.variants.zero_is_always_limit_point`
and `erdos_problem_1151.variants.not_for_all_x` below.

The main statement `erdos_problem_1151` therefore formalizes the one reading
the page itself supports: the [Er43] claim, with $x = \cos(\pi p/q)$ for odd
$p, q \geq 1$ (such $x$ are never Chebyshev nodes: node angles have even
reduced denominator, these have odd), and $A$ restricted to closed subsets of
$[-1,1]$ as in the displayed statement. The remark's literal claim for an
arbitrary closed $A \subseteq \mathbb{R}$ is
`erdos_problem_1151.variants.er43_arbitrary_closed`.

## References

Recovered from the original pipeline's fetch of erdosproblems.com/latex/1151
(preserved in the session logs as a structured extraction, not raw HTML;
volume numbers were absent and are deliberately not invented):

- [Er41] Erdős, P., _On divergence properties of the Lagrange interpolation
  parabolas_. Annals of Mathematics, Series 2 (1941), 309–315.
- [Er43] The site's `/latex/1151` bibliography expands this (site-global) key
  as: Erdős, P., _A note on Farey series_. Quarterly Journal of Mathematics,
  Oxford Series (1943), 82–85 — the same expansion recovered independently
  for problem #1005, which shares the key. CAVEAT: that paper is about Farey
  fractions and cannot topically contain the interpolation claim cited here;
  the intended paper is presumably Erdős's 1943 interpolation paper
  ("On some convergence properties of the interpolation polynomials",
  reviewer knowledge, NOT verified against the site). Recorded as the site
  serves it, with this caveat; nothing invented.
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest, July 1999
  (1999). This problem: §2.41. (Corpus-canonical identity; the archived
  styled copy's gloss "Varga, R.S., *Scientific Computation on Mathematical
  Problems and Conjectures*, 1999" is a hallucinated attribution contradicted
  by the recovered `/latex/1151` extraction.)

NOTE: the fixed main statement and the variants below are from the Fable
review of 2026-08-14 and are **not compile-verified** (the review container
cannot run `lake build`). The *input* file `conjectures/1151.lean` compiled
successfully in its originating session (sole warning: the expected `sorry`).

Tags: analysis, polynomials
-/

/-- The k-th Chebyshev node of order n (0-indexed):
    cos((2k + 1)π / (2n)) for k = 0, ..., n-1. -/
noncomputable def chebyshevNode (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (n : ℝ)))

/-- The Lagrange basis polynomial ℓ_i(x) = ∏_{j≠i} (x - x_j)/(x_i - x_j).

    (Factorwise division: each factor's denominator is nonzero whenever the
    nodes are pairwise distinct, which holds for the Chebyshev nodes — the
    only nodes this file uses.) -/
noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  ∏ j ∈ univ.erase i, (x - nodes j) / (nodes i - nodes j)

/-- The Lagrange interpolation of f at the given nodes, evaluated at x:
    L(x) = ∑_i f(x_i) · ℓ_i(x). -/
noncomputable def lagrangeInterp {n : ℕ} (nodes : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, f (nodes i) * lagrangeBasis nodes i x

/-- The set of limit points (cluster points) of a sequence of reals.
    A real y is a limit point of a if for every ε > 0 and every N,
    there exists n ≥ N with |a(n) - y| < ε.

    (Equivalent to Mathlib's `{y | MapClusterPt y atTop a}`; kept as a local
    def matching the input file.) -/
def limitPoints (a : ℕ → ℝ) : Set ℝ :=
  {y : ℝ | ∀ ε > 0, ∀ N : ℕ, ∃ n, N ≤ n ∧ |a n - y| < ε}

/--
Erdős Problem #1151 [Va99, 2.41] (Open):
For x = cos(πp/q) with p, q ≥ 1 odd integers, and any closed A ⊆ [-1,1],
there exists a continuous function f such that A is the set of limit points
of the Lagrange interpolation polynomials Lⁿf(x) at the Chebyshev nodes as
n → ∞.

This is the [Er43] claim reported on the page ("for specific x of this
shape"), with A restricted to closed subsets of [-1,1] as in the displayed
statement. The displayed statement leaves x free and the site owner is
"unclear exactly what is intended"; the first-pass reading "for all
x ∈ [-1,1]" is provably false — see
`erdos_problem_1151.variants.not_for_all_x`.

(`Odd p` over ℕ forces p ≥ 1, matching the page's "odd integers p, q ≥ 1";
q ≥ 1 also makes the division πp/q well-defined. Global continuity of f on ℝ
is equivalent to continuity on [-1,1] here by Tietze extension, since only
values at the nodes matter.)
-/
theorem erdos_problem_1151 (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (A : Set ℝ) (hA : IsClosed A) (hAsub : A ⊆ Set.Icc (-1 : ℝ) 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      limitPoints (fun n => lagrangeInterp (chebyshevNode (n + 1)) f
        (Real.cos (Real.pi * (p : ℝ) / (q : ℝ)))) = A :=
  sorry

/--
[Er41] (solved, Erdős 1941): if x = cos(πp/q) for odd integers p, q ≥ 1, then
there is a continuous function f with lim_{n→∞} Lⁿf(x) = ∞ over the sequence
of Chebyshev nodes. Page-confirmed remark; this is the divergence result that
realizes A = ∅ at such x. Not compile-verified.
-/
theorem erdos_problem_1151.variants.er41_divergence (p q : ℕ) (hp : Odd p) (hq : Odd q) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      Filter.Tendsto (fun n => lagrangeInterp (chebyshevNode (n + 1)) f
        (Real.cos (Real.pi * (p : ℝ) / (q : ℝ)))) Filter.atTop Filter.atTop :=
  sorry

/--
The obstruction refuting the "for all x ∈ [-1,1]" reading: for every
f : ℝ → ℝ (continuous or not), f(0) is a limit point of the sequence
Lⁿf(0). Reason: 0 is a Chebyshev node of every odd order m (index
k = (m-1)/2 gives cos((2k+1)π/(2m)) = cos(π/2) = 0); the Chebyshev nodes of
a given order are pairwise distinct, so ℓ_k(0) = 1 and ℓ_i(0) = 0 for i ≠ k,
whence Lᵐf(0) = f(0) for all odd m — a constant subsequence. Provable
(elementary); stated with `sorry` in this pipeline. Not compile-verified.
-/
theorem erdos_problem_1151.variants.zero_is_always_limit_point (f : ℝ → ℝ) :
    f 0 ∈ limitPoints (fun n => lagrangeInterp (chebyshevNode (n + 1)) f 0) :=
  sorry

/--
The first-pass formalization's reading — "for **all** x ∈ [-1,1] and all
closed A ⊆ [-1,1] there is a continuous f with limit-point set A" — is
FALSE: instantiate at x = 0 and A = ∅ and apply
`erdos_problem_1151.variants.zero_is_always_limit_point`. Provable
(elementary); stated with `sorry` in this pipeline. Not compile-verified.
-/
theorem erdos_problem_1151.variants.not_for_all_x :
    ¬ (∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ A : Set ℝ, IsClosed A → A ⊆ Set.Icc (-1 : ℝ) 1 →
      ∃ f : ℝ → ℝ, Continuous f ∧
        limitPoints (fun n => lagrangeInterp (chebyshevNode (n + 1)) f x) = A) :=
  sorry

/--
The [Er43] claim in the page remark's literal form: for x = cos(πp/q) with
p, q ≥ 1 odd and **any** closed A ⊆ ℝ (not necessarily contained in [-1,1]),
there is a continuous f whose Lⁿf(x) has limit-point set exactly A. (Lagrange
interpolants of a bounded function need not stay in [-1,1] — the Lebesgue
constants of the Chebyshev nodes grow like log n — so unbounded closed A are
not obviously excluded.) Open. Not compile-verified.
-/
theorem erdos_problem_1151.variants.er43_arbitrary_closed (p q : ℕ) (hp : Odd p)
    (hq : Odd q) (A : Set ℝ) (hA : IsClosed A) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      limitPoints (fun n => lagrangeInterp (chebyshevNode (n + 1)) f
        (Real.cos (Real.pi * (p : ℝ) / (q : ℝ)))) = A :=
  sorry

end Erdos1151
