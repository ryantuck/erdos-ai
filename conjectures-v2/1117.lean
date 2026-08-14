import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #1117

Source: https://www.erdosproblems.com/1117 (page last edited 29 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "Let $f(z)$ be an entire function which is not a monomial.
Let $\nu(r)$ count the number of $z$ with $\lvert z\rvert=r$ such that
$\lvert f(z)\rvert=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$. (This is a finite
quantity if $f$ is not a monomial.)

Is it possible for \[\limsup \nu(r)=\infty?\] Is it possible for
\[\liminf \nu(r)=\infty?\]"

Status: OPEN (banner tooltip: "This is open, and cannot be resolved with a
finite computation."). Tag: analysis. Attribution: [Ha74].

Remarks from the page:

* "This is Problem 2.16 in [Ha74], where it is attributed to Erdős."
* "The answer to the first question is yes, as shown by Herzog and Piranian
  [HePi68]. The second question is still open, although an 'approximate'
  affirmative answer is given by Glücksam and Pardo-Simón [GlPa24]." (The
  'approximate' result of [GlPa24] is recorded in prose only; the page does not
  state it precisely enough to formalize.)

Encoding notes. The problem box asks **two** yes/no questions — the $\limsup$
question (answered YES by [HePi68]) and the $\liminf$ question (OPEN). This
raw-file corpus has no `answer()` elaborator (a formal-conjectures construct),
so, following the corpus convention, each question is stated as a direct
assertion of a definite direction:

* `erdos_problem_1117` (the open $\liminf$ question) asserts the affirmative
  direction — an entire non-monomial $f$ with $\nu(r)\to\infty$ exists. The
  page records no explicit conjectured direction, but the affirmative is the
  substantive existence claim, is parallel to the $\limsup$ question already
  answered yes, and is what the 'approximate' affirmative answer of [GlPa24]
  points toward. If the true answer is "no", the statement is false; what is
  open is the question itself.
* `erdos_problem_1117.variants.herzog_piranian_limsup` (the solved $\limsup$
  question) asserts the true direction, proved by [HePi68].

$\liminf_{r\to\infty}\nu(r)=\infty$ is encoded as
$\forall N\,\exists R\,\forall r\ge R,\ \nu(r)\ge N$ (i.e. $\nu(r)\to\infty$;
for an ℕ-valued function these are the same). $\limsup_{r\to\infty}\nu(r)=
\infty$ is encoded as $\forall N\,\forall R\,\exists r\ge R,\ \nu(r)\ge N$
($\nu(r)\ge N$ at arbitrarily large radii — deliberately *not* mere
unboundedness of $\nu$ over all $r$, which would in principle also be
satisfiable by radii from a bounded set).

The source's parenthetical "(This is a finite quantity if $f$ is not a
monomial.)" is a theorem, not a hypothesis: if $\lvert f\rvert$ were constant
on some circle $\lvert z\rvert = r > 0$ then $f$ would be a monomial (for
nonzero constant modulus, $f$ agrees on the disc with a constant times a finite
Blaschke product, whose entirety forces all zeros to sit at the origin, i.e.
$f = cz^m$; for constant modulus $0$ the identity theorem gives $f \equiv 0$,
a monomial with $c = 0$). So for non-monomial entire $f$ the map
$\theta \mapsto \lvert f(re^{i\theta})\rvert$ is a non-constant real-analytic
function and its maximum set is finite and nonempty; `Set.ncard` is therefore
the honest count wherever the theorems evaluate it. All junk values push
*against* the asserted property, never toward a degenerate witness: for
$r < 0$ the sphere is empty, `maxModulus` is `sSup ∅ = 0` (Real junk value)
and `nu` is `0`; an infinite argmax set (impossible here, but in general)
would make `ncard` return `0`. Hence the statements are not vacuously
satisfiable.

References (keys from the page; authors, titles, journal, years, and pages
recovered from the site's `/latex/1117` bibliography via the session logs;
volume numbers were not in the recovered data and are omitted rather than
invented):

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_
(1974), 155–180.

[HePi68] Herzog, F. and Piranian, G., _The counting function for points of
maximum modulus_ (1968), 240–243.

[GlPa24] Glücksam, Adi and Pardo-Simón, Leticia, _An approximate solution to
Erdős' maximum modulus points problem_. J. Math. Anal. Appl. (2024), Paper
No. 127768, 20 pp.

Formalised statement in external databases: No (as of the archived capture).
No related OEIS sequences or cross-referenced problems are listed. The page
shows one forum comment; its content is not in the archived capture.
-/

noncomputable section
open Complex Set

namespace Erdos1117

/-- A function f : ℂ → ℂ is a monomial if f(z) = c * z^n for some constant c
    and natural number n. This includes constants (n = 0) and the zero
    function (c = 0) — exactly the entire functions whose modulus is constant
    on every circle centered at the origin, which the problem excludes. -/
def IsMonomial (f : ℂ → ℂ) : Prop :=
  ∃ (c : ℂ) (n : ℕ), ∀ z, f z = c * z ^ n

/-- The maximum modulus of f on the circle of radius r:
    M(r) = sup{‖f(z)‖ : ‖z‖ = r}. For continuous f and r ≥ 0 the set is the
    image of a compact nonempty circle, so the supremum is attained; for r < 0
    the set is empty and `sSup` returns the Real junk value 0 (harmless here —
    it only makes negative radii fail the theorems' conditions). -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- ν(r) counts the number of z with ‖z‖ = r achieving the maximum modulus
    of f. This is finite (and, for r > 0, nonzero) when f is entire and not a
    monomial — see the module docstring; `Set.ncard` returns 0 on an infinite
    set, a junk value that could only make the theorems below harder, not
    vacuously true. -/
noncomputable def nu (f : ℂ → ℂ) (r : ℝ) : ℕ :=
  ncard {z : ℂ | ‖z‖ = r ∧ ‖f z‖ = maxModulus f r}

/--
Erdős Problem #1117 [Ha74] — OPEN (this is Problem 2.16 in [Ha74], where it
is attributed to Erdős)

Let f(z) be an entire function which is not a monomial. Let ν(r) count the
number of z with |z| = r such that |f(z)| = max_{|z|=r} |f(z)|.
(This is a finite quantity if f is not a monomial.)

The page asks two questions: is it possible for limsup ν(r) = ∞ (answered yes
by Herzog and Piranian [HePi68] — see
`erdos_problem_1117.variants.herzog_piranian_limsup`), and is it possible for
liminf ν(r) = ∞? This theorem is the second, still-open question, asserted in
the affirmative direction (see the module docstring's encoding note): there
exists an entire non-monomial f with ν(r) → ∞, i.e. for every N, ν(r) ≥ N for
all sufficiently large r. An 'approximate' affirmative answer is given by
Glücksam and Pardo-Simón [GlPa24].
-/
theorem erdos_problem_1117 :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ¬IsMonomial f ∧
      ∀ N : ℕ, ∃ R : ℝ, ∀ r : ℝ, R ≤ r → N ≤ nu f r :=
  sorry

/--
The first question of the problem box (page-confirmed, SOLVED — "The answer to
the first question is yes, as shown by Herzog and Piranian [HePi68]"): there
exists an entire function f, not a monomial, with limsup_{r→∞} ν(r) = ∞,
encoded as: for every N, radii r with ν(r) ≥ N exist beyond every bound R.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1117.variants.herzog_piranian_limsup :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ¬IsMonomial f ∧
      ∀ (N : ℕ) (R : ℝ), ∃ r : ℝ, R ≤ r ∧ N ≤ nu f r :=
  sorry

end Erdos1117
