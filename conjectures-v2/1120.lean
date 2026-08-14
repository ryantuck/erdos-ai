import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Erdős Problem #1120

Source: https://www.erdosproblems.com/1120 (page last edited 30 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "Let $f\in \mathbb{C}[z]$ be a monic polynomial of degree
$n$, all of whose roots satisfy $\lvert z\rvert\leq 1$. Let
\[E= \{ z : \lvert f(z)\rvert \leq 1\}.\]
What is the shortest length of a path in $E$ joining $z=0$ to
$\lvert z\rvert =1$?"

Status: OPEN (banner tooltip: "This is open, and cannot be resolved with a
finite computation."). Tag: analysis. Attribution: [Ha74].

Remarks from the page:

* "This is Problem 4.22 in [Ha74], where it is attributed to Erdős. In [Ha74]
  it is reported that Clunie and Netanyahu (personal communication) showed
  that a path always exists which joins $z=0$ to $\lvert z\rvert=1$ in $A$."
  (The page writes "$A$" although its own notation names the set $E$ — an
  evident typo for $E$.)
* "Erdős wrote 'presumably this tends to infinity with $n$, but not too
  fast'."
* "The trivial lower bound for the length of this path is $1$, which is
  achieved for $f(z)=z^n$. The interesting side of this question is what the
  worst case behaviour is (as a function of $n$)."
* "See also [1041]." (Erdős Problem #1041 — paths of length $<2$ joining two
  roots inside $\{z : \lvert f(z)\rvert < 1\}$ — is `conjectures-v2/1041.lean`
  in this corpus.)

Encoding notes. The problem box literally asks a value request ("What is the
shortest length…?") whose answer depends on $f$; the page's remarks identify
the formalizable core as the worst-case behaviour, over admissible $f$ of
degree $n$, of the shortest connecting path length, together with Erdős's
conjecture that it tends to infinity with $n$. This raw-file corpus has no
`answer()` elaborator (a formal-conjectures construct), so — following the
corpus convention for open problems with a stated expected direction (cf.
`conjectures-v2/1117.lean`, `conjectures-v2/1041.lean`) — `erdos_problem_1120`
asserts Erdős's conjectured direction directly: for every $C>0$ and all
sufficiently large $n$ there is an admissible $f$ of degree $n$ forcing every
path in $E$ from $0$ to the unit circle to have arc length $\geq C$. Writing
$W(n)$ for the sup over admissible $f$ of degree $n$ of the infimum of
connecting path lengths, this is equivalent to $W(n)\to\infty$ (for one
direction instantiate at $C+1$; exhibiting one $f$ whose every path has
length $\geq C$ gives $W(n)\geq C$). Erdős's qualitative "but not too fast"
carries no precise growth bound and is not formalized.

Non-vacuity guards: $0\in E$ always, since for monic $f$ with roots
$r_1,\dots,r_n$ in the closed unit disk $|f(0)|=\prod_i|r_i|\leq 1$; and by
the Clunie–Netanyahu result (see the variant) an admissible path always
exists, so the universal quantifier over paths in the main theorem is not
satisfied vacuously. (Even hypothetically, an $f$ admitting no connecting
path would have shortest length $\inf\varnothing=+\infty\geq C$, so such an
$f$ would be a legitimate witness under the informal reading as well.) Arc
length is encoded as the total variation `eVariationOn γ (Icc 0 1)` valued in
`ℝ≥0∞` — the arc length for rectifiable paths and `⊤` otherwise. Paths are
globally continuous `γ : ℝ → ℂ` constrained on `Icc 0 1`; this is equivalent
to quantifying over continuous paths on `[0,1]`, since any such path extends
to ℝ by constants with the same variation on `Icc 0 1`.

References (key from the page. Bibliographic data recovered from the site's
`/latex/1117` and `/latex/1118` bibliography fetches preserved in the session
logs — the key is shared sitewide; no `/latex/1120` fetch was captured.
Publisher/volume data were absent from the recovered material and are omitted
rather than invented):

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_
(1974), 155–180.

Formalised statement in external databases: No (as of the archived capture).
No related OEIS sequences. Cross-referenced problem: [1041].
-/

noncomputable section
open Complex Polynomial Set

namespace Erdos1120

/-- The lemniscate (sublevel) set of a polynomial f: {z ∈ ℂ : ‖f(z)‖ ≤ 1}. -/
def lemniscateSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

/--
Erdős Problem #1120 [Ha74, Problem 4.22] — OPEN.

Let f ∈ ℂ[z] be a monic polynomial of degree n, all of whose roots satisfy
|z| ≤ 1. Let E = {z : |f(z)| ≤ 1}. The page asks: what is the shortest length
of a path in E joining z = 0 to |z| = 1? Per the page's remarks, the
formalizable core is the worst-case behaviour in n, and this theorem asserts
Erdős's conjectured direction — "presumably this tends to infinity with n,
but not too fast" — i.e. the worst-case shortest length tends to infinity
with n (see the module docstring's encoding notes).

The trivial lower bound is 1, achieved by f(z) = z^n (see the variants).
Clunie and Netanyahu (personal communication reported in [Ha74]) showed that
a path joining z = 0 to |z| = 1 in E always exists.

Formally: for every C > 0, there exists N such that for all n ≥ N, there is a
monic polynomial f of degree n with all roots in the closed unit disk, such
that every continuous path γ : [0,1] → E from 0 to the unit circle has arc
length ≥ C.
-/
theorem erdos_problem_1120 :
    ∀ C : ℝ, C > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ f : Polynomial ℂ, f.Monic ∧ f.natDegree = n ∧
      (∀ z ∈ f.roots, ‖z‖ ≤ 1) ∧
      ∀ γ : ℝ → ℂ, Continuous γ →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ lemniscateSet f) →
        γ 0 = 0 →
        ‖γ 1‖ = 1 →
        ENNReal.ofReal C ≤ eVariationOn γ (Icc (0 : ℝ) 1) :=
  sorry

/--
Clunie–Netanyahu path-existence result (page-confirmed, reported as solved:
"In [Ha74] it is reported that Clunie and Netanyahu (personal communication)
showed that a path always exists which joins z = 0 to |z| = 1 in [E]"): for
every monic f with all roots in the closed unit disk, some continuous path
inside E = {z : |f(z)| ≤ 1} joins the origin to the unit circle. (For
degree 0 the statement is trivial: f = 1 and E = ℂ.)

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1120.variants.clunie_netanyahu :
    ∀ f : Polynomial ℂ, f.Monic → (∀ z ∈ f.roots, ‖z‖ ≤ 1) →
      ∃ γ : ℝ → ℂ, Continuous γ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ lemniscateSet f) ∧
        γ 0 = 0 ∧ ‖γ 1‖ = 1 :=
  sorry

/--
The trivial lower bound (page-confirmed: "The trivial lower bound for the
length of this path is 1"): every continuous path from the origin to the unit
circle has arc length at least 1. The bound is purely metric — total
variation dominates the distance between the endpoints — so no hypothesis on
a polynomial or on membership in a lemniscate set is needed.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1120.variants.trivial_lower_bound :
    ∀ γ : ℝ → ℂ, Continuous γ → γ 0 = 0 → ‖γ 1‖ = 1 →
      ENNReal.ofReal 1 ≤ eVariationOn γ (Icc (0 : ℝ) 1) :=
  sorry

/--
The trivial lower bound is attained for f(z) = zⁿ (page-confirmed: "which is
achieved for f(z) = z^n"): for f = Xⁿ the lemniscate set contains the closed
unit disk (for t ∈ [0,1], |tⁿ| ≤ 1), and the radial segment γ(t) = t joins 0
to the unit circle inside it with arc length exactly 1.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1120.variants.trivial_bound_attained (n : ℕ) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ lemniscateSet ((X : Polynomial ℂ) ^ n)) ∧
      γ 0 = 0 ∧ ‖γ 1‖ = 1 ∧
      eVariationOn γ (Icc (0 : ℝ) 1) = ENNReal.ofReal 1 :=
  sorry

end Erdos1120
