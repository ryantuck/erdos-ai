import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #1118

Source: https://www.erdosproblems.com/1118 (page last edited 29 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "Let $f(z)$ be a non-constant entire function such that,
for some $c$, the set $E(c)=\{ z: \lvert f(z)\rvert > c\}$ has finite measure.

What is the minimum growth rate of $f(z)$?

If $E(c)$ has finite measure then must there exist $c'<c$ such that $E(c')$
has finite measure?"

Status: SOLVED (banner tooltip: "This has been resolved in some other way than
a proof or disproof."). Tag: analysis. Attribution: [Ha74].

Remarks from the page:

* "This is Problem 2.40 in [Ha74] where it is attributed to Erdős. Hayman
  conjectured that \[\int_0^\infty \frac{r}{\log\log M(r)}\mathrm{d}r<\infty\]
  is true, and best possible, where
  $M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$."
* "Hayman's strong conjecture was proved independently by Camera [Ca77] and
  Gol'dberg [Go79b]."
* "The second question was answered in the negative by Gol'dberg [Go79b], who
  proved that if $T=\{ c>0 : \lvert E(c)\rvert <\infty\}$ then for any $m>0$
  there exist entire functions $f$ such that $T=[m,\infty)$ or $T=(m,\infty)$.
  (It is clear that $T=\emptyset$ and $T=(0,\infty)$ are also possible.)"

Encoding notes:

* The first question is a soft value request ("What is the minimum growth
  rate?") which the page resolves to Hayman's integral condition, proved by
  Camera and Gol'dberg; it is stated here as a direct assertion of the proved
  theorem (`erdos_problem_1118_growth_rate`). The second question is a yes/no
  question answered in the negative; it is stated as a direct assertion of the
  true direction, i.e. the existence of a counterexample
  (`erdos_problem_1118_negative_answer`).
* **Lower-endpoint correction.** The page writes the integral as
  $\int_0^\infty$, but read literally over all of $(0,\infty)$ (with Lean's
  total `Real.log` and junk values at the finitely many bad points) the
  integrability claim is FALSE for some functions in the hypothesis class:
  if $M(r)$ crosses the value $e$ at some radius $r_0 > 0$ (which happens
  whenever $\lVert f(0)\rVert < e$, e.g. after replacing an admissible $f$
  by $f/A$ for large $A$ — this rescales $E_f(c)$ to $E_{f/A}(c/A)$ and
  preserves the hypotheses), then $\log\log M(r) \le K(r-r_0)$ just above
  $r_0$ (local Lipschitzness of $\log M$, from Hadamard three-circles
  convexity, composed with $\log$ near $\log M(r_0)=1$), so the integrand
  dominates $r_0/(K(r-r_0))$ and is not integrable near $r_0$. The intended
  (and true) content is convergence of the integral *at infinity*, so the
  conclusion is stated as integrability on $(r_0, \infty)$ for some $r_0$.
  This matches the informal convention under which the printed
  $\int_0^\infty$ ignores the (bounded) region where $\log\log M$ is
  undefined. The fix is NOT compile-verified (no `lake build` available in
  the review container).
* "Best possible" in Hayman's conjecture is recorded in prose only; the page
  does not state it precisely enough to formalize, and it is not formalized
  here.
* Gol'dberg's fuller structure theorem for the threshold set $T$ is
  page-confirmed and added as
  `erdos_problem_1118.variants.goldberg_threshold_sets`.

References (keys from the page; bibliographic data recovered from the original
pipeline's fetch of the site's `/latex/1118` bibliography, preserved in the
session logs; volume numbers were not in the recovered data and are omitted
rather than invented):

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_
(1974), 155–180.

[Ca77] Camera, G., _On the minimum rate of growth of certain classes on
integral and subharmonic functions_, PhD Thesis, Imperial College, University
of London (1977).

[Go79b] Gol'dberg, A. A., _Sets on which the modulus of an entire function has
a lower bound_, Sibirsk. Mat. Zh. (1979), 512–518, 691.

Formalised statement in external databases: No (as of the archived capture).
No related OEIS sequences or cross-referenced problems are listed; the page
shows 0 forum comments.
-/

noncomputable section
open Complex Set MeasureTheory

namespace Erdos1118

/-- The maximum modulus of f on the circle of radius r:
    M(r) = sup{‖f(z)‖ : ‖z‖ = r}. For continuous f and r ≥ 0 the set is the
    image of a compact nonempty circle, so the supremum is attained (at r = 0
    it is ‖f 0‖); for r < 0 the set is empty and `sSup` returns the Real junk
    value 0, which is harmless since the theorems below only evaluate it on
    tails of (0, ∞). -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- The exceedance set E(c) = {z : ℂ | ‖f(z)‖ > c}. -/
def exceedanceSet (f : ℂ → ℂ) (c : ℝ) : Set ℂ :=
  {z : ℂ | c < ‖f z‖}

/--
Erdős Problem #1118 — Part 1 (Hayman's conjecture, this is Problem 2.40 in
[Ha74]; proved independently by Camera [Ca77] and Gol'dberg [Go79b]):

Let f(z) be a non-constant entire function such that for some c > 0, the set
E(c) = {z : |f(z)| > c} has finite (Lebesgue) measure. Then
  ∫^∞ r / (log log M(r)) dr < ∞
where M(r) = max_{|z|=r} |f(z)|, i.e. the integral converges at infinity:
there is an r₀ beyond which the integrand is integrable. (Hayman also
conjectured this growth condition to be best possible; the page records that
in prose only and it is not formalized here.)

The source page prints the integral as ∫₀^∞, but over the whole of (0, ∞)
the statement is literally false for members of the hypothesis class whose
maximum modulus crosses e at some radius r₀ > 0 (e.g. any admissible f
rescaled so that ‖f(0)‖ < e): near such a crossing log log M(r) ≤ K(r − r₀),
so the integrand dominates a non-integrable r₀/(K(r − r₀)) — Lean's junk
values at the isolated bad points do not repair a genuine non-integrable
singularity. Hence the ∃ r₀ tail form, which is the intended content.
NOTE: this correction is not compile-verified.
-/
theorem erdos_problem_1118_growth_rate (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hnc : ∃ z : ℂ, f z ≠ f 0)
    (c : ℝ) (hc : 0 < c)
    (hfin : volume (exceedanceSet f c) < ⊤) :
    ∃ r₀ : ℝ, IntegrableOn (fun r => r / Real.log (Real.log (maxModulus f r)))
      (Ioi r₀) volume :=
  sorry

/--
Erdős Problem #1118 — Part 2 (Gol'dberg [Go79b]):

The answer to the second question is negative: there exists a non-constant
entire function f and c > 0 such that E(c) has finite measure, but E(c') has
infinite measure for all 0 < c' < c. (Such an f is furnished by Gol'dberg's
threshold sets T = [m, ∞) with c = m — see
`erdos_problem_1118.variants.goldberg_threshold_sets`. Restricting to
c' > 0 loses nothing: for c' ≤ 0 the set E(c') always has infinite measure
for non-constant entire f.)
-/
theorem erdos_problem_1118_negative_answer :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z : ℂ, f z ≠ f 0) ∧
      ∃ c : ℝ, 0 < c ∧
        volume (exceedanceSet f c) < ⊤ ∧
        ∀ c' : ℝ, 0 < c' → c' < c → volume (exceedanceSet f c') = ⊤ :=
  sorry

/--
Gol'dberg's threshold-set structure theorem [Go79b] (page-confirmed): writing
T = {c > 0 : |E(c)| < ∞} for the set of admissible thresholds, for any m > 0
there exist non-constant entire functions realizing T = [m, ∞), and there
exist non-constant entire functions realizing T = (m, ∞). (The page adds that
T = ∅ and T = (0, ∞) are clearly also possible; those trivial cases are not
formalized.) The closed case T = [m, ∞) is what witnesses the negative answer
in `erdos_problem_1118_negative_answer`; the open case T = (m, ∞) does not
(every c ∈ (m, ∞) admits a smaller c' ∈ (m, c) still in T).

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1118.variants.goldberg_threshold_sets
    (m : ℝ) (hm : 0 < m) :
    (∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z : ℂ, f z ≠ f 0) ∧
      {c : ℝ | 0 < c ∧ volume (exceedanceSet f c) < ⊤} = Ici m) ∧
    (∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z : ℂ, f z ≠ f 0) ∧
      {c : ℝ | 0 < c ∧ volume (exceedanceSet f c) < ⊤} = Ioi m) :=
  sorry

end Erdos1118
