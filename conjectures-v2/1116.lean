import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #1116

Source: https://www.erdosproblems.com/1116 (archived capture accessed
2026-02-23; no page-edition date appears in the capture).

Verbatim statement: "For a meromorphic function $f$ let $n(r,a)$ count the
number of roots of $f(z)=a$ in the disc $\lvert z\rvert <r$. Does there exist
a meromorphic (or entire) $f$ such that for every $a\neq b$
\[\limsup_{r\to \infty}\frac{n(r,a)}{n(r,b)}=\infty?\]"

Status: SOLVED (banner tooltip: "This has been resolved in some other way than
a proof or disproof."). Tag: analysis.

Remarks from the page:

* "This is Problem 1.25 in [Ha74], where it is attributed to Erdős."
* "Gol'dberg [Go78] and Toppila [To76] have constructed entire functions with
  this property."

Encoding notes. The question is a yes/no existence question, answered YES by
the entire-function constructions of [Go78] and [To76]; this raw corpus has no
answer-elaborator, so the theorem asserts the true direction directly. Since
the page's disjunctive "meromorphic (or entire)" is answered affirmatively by
entire witnesses, and entire functions are a subclass of meromorphic ones,
formalizing the entire case is the strongest reading and settles the question
as posed; no separate meromorphic variant is stated (it would require
meromorphic-function machinery not present in this file). The
$\limsup = \infty$ condition is encoded multiplicatively
($\forall M\,\forall R\,\exists r > R,\ M\cdot n(r,b) < n(r,a)$), which also
handles radii with $n(r,b) = 0$ correctly (there it demands $n(r,a) > 0$,
matching the informal convention that a positive count divided by zero is
$\infty$). Note the condition is required for *ordered* pairs, so both
$\limsup n(r,a)/n(r,b) = \infty$ and $\limsup n(r,b)/n(r,a) = \infty$ hold for
every pair — exactly as the source's "for every $a \neq b$" demands (possible
simultaneously because these are limsups, not limits). A consequence worth
recording: the property forces $f$ to attain every complex value — if $f$
omitted $a$ then $n(r,a) = 0$ for all $r$ and the pair $(a, b)$ would fail —
which is consistent with Picard's theorem leaving room for such $f$.

Counting convention: `rootCount` counts *distinct* solutions (`Set.ncard`),
i.e. the source's "number of roots" read without multiplicity (the Nevanlinna
counting function $n(r,a)$ is traditionally counted *with* multiplicity; the
source page does not specify, and the distinct-roots reading is the literal
one). See the `rootCount` docstring.

References (keys from the page; authors, titles, journals, years, and pages
recovered from the site's `/latex/1116` bibliography via the session logs;
volume numbers were not in the recovered data and are omitted rather than
invented):

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_
(1974), 155–180.

[Go78] Gol'dberg, A. A., _Counting functions of sequences of a-points for
entire functions_. Sibirsk. Mat. Zh. (1978), 28–36, 236.

[To76] Toppila, Sakari, _On the counting function for the a-values of a
meromorphic function_. Ann. Acad. Sci. Fenn. Ser. A I Math. (1976), 565–572.

Formalised statement in external databases: No (as of the archived capture).
No related OEIS sequences or cross-referenced problems are listed.
-/

noncomputable section
open Complex Set

namespace Erdos1116

/-- The counting function n(r, a) for f: the number of solutions to f(z) = a
    in the open disk {z : ℂ | ‖z‖ < r}, counted *without* multiplicity
    (`Set.ncard`, natural cardinality). For a nonconstant entire f the solution
    set is discrete, hence finite in every bounded disk, so `ncard` is the
    honest count; for constant f the set is empty or an infinite disk, and
    `ncard` returns 0 in both cases (junk value on the infinite case — harmless
    here, since it only makes constant functions fail the theorem's condition,
    which they must). NOTE: the traditional Nevanlinna counting function counts
    with multiplicity; the source says only "the number of roots", and this
    file formalizes the literal distinct-roots reading. -/
def rootCount (f : ℂ → ℂ) (r : ℝ) (a : ℂ) : ℕ :=
  ncard {z : ℂ | f z = a ∧ ‖z‖ < r}

/--
Erdős Problem #1116 (SOLVED — this is Problem 1.25 in [Ha74], where it is
attributed to Erdős; Gol'dberg [Go78] and Toppila [To76] have constructed
entire functions with this property):

For a meromorphic function f, let n(r,a) count the number of roots of f(z) = a
in the disc |z| < r. Does there exist a meromorphic (or entire) f such that
for every a ≠ b, limsup_{r→∞} n(r,a)/n(r,b) = ∞?

Answered yes, with entire witnesses; the entire case is formalized (it settles
the "meromorphic (or entire)" question as posed).

The limsup = ∞ condition is expressed multiplicatively: for every M and R,
there exists r > R with n(r,a) > M · n(r,b). This also covers radii where
n(r,b) = 0, requiring n(r,a) > 0 there.
-/
theorem erdos_problem_1116 :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ a b : ℂ, a ≠ b →
        ∀ (M : ℝ) (R : ℝ), ∃ r : ℝ, r > R ∧
          M * (rootCount f r b : ℝ) < (rootCount f r a : ℝ) :=
  sorry

end Erdos1116
