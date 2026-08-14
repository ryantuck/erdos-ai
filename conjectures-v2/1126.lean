import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

/-!
# Erdős Problem #1126

Source: https://www.erdosproblems.com/1126 (full archived HTML capture, accessed
2026-02-23, recovered from the session logs; two verbatim copies inside that capture
agree on every field). Page edition: 30 December 2025.

Verbatim statement: "If \[f(x+y)=f(x)+f(y)\] for almost all $x,y\in \mathbb{R}$ then
there exists a function $g$ such that \[g(x+y)=g(x)+g(y)\] for all
$x,y\in\mathbb{R}$ such that $f(x)=g(x)$ for almost all $x$."
(The second "such that" plainly means "and"; the docstring below renders it so.)

Status: PROVED (banner tooltip: "This has been solved in the affirmative.").
Problem source: [Er60c]. Tag: analysis.

Remarks from the page (verbatim): "Proved independently by de Bruijn [dB66] and
Jurkat [Ju65]."

Capture note: a later structured re-capture in the upstream formal-conjectures logs
reported the banner as "PROVED (LEAN)" while simultaneously reporting "No formalised
statement currently exists" — internally inconsistent, and contradicted by the raw
HTML capture (plain PROVED, "Formalised statement? No") at the identical page
edition. The raw HTML is treated as authoritative here; either way the problem is
solved in the affirmative.

Encoding notes.

1. The source states the problem as a direct assertion (Erdős's conjecture, since
   proved), and the theorem asserts it directly — the true direction, per de Bruijn
   [dB66] and Jurkat [Ju65]. No `answer()` wrapper exists in this raw corpus.
2. "For almost all $x,y \in \mathbb{R}$" is encoded as a.e. with respect to the
   product Lebesgue measure on ℝ × ℝ (`volume.prod volume`), i.e. planar Lebesgue
   measure — the standard reading of the de Bruijn/Jurkat theorem. This is the
   measure the ambient `MeasureSpace (ℝ × ℝ)` instance carries, written explicitly
   for clarity. No measurability of `f` is assumed, correctly: the theorem does not
   require it.
3. "For almost all $x$" in the conclusion is one-dimensional Lebesgue a.e.
   (`∀ᵐ x ∂volume`), distinct from the planar a.e. of the hypothesis, as in the
   source.

References (keys as on the recovered page; [dB66]/[Ju65] bibliographic data
recovered from the archived WebFetch of erdosproblems.com/latex/1126 in the
upstream session logs — the [Ju65] volume number 16 additionally carried over from
the upstream styled file and consistent with reviewer knowledge; the [dB66] volume
number was absent from the extraction and is NOT supplied here):

[Er60c] Erdős, P. (c. 1960). Original problem source — full bibliographic details
not recoverable from the archived captures (honest stub; the /latex extraction
contained no entry for this key).

[dB66] de Bruijn, N.G., _On almost additive functions_. Colloq. Math. (1966),
59-63.

[Ju65] Jurkat, W.B., _On Cauchy's functional equation_. Proc. Amer. Math. Soc. 16
(1965), 683-686.

(An earlier upstream draft attributed [dB66] to "A difference property for Riemann
integrable functions and for some similar classes of functions, Indag. Math. 28
(1966), 145-151" — a fabricated hybrid of a different, 1952 de Bruijn paper's title
and pages with the 1966 year; the upstream pipeline itself later corrected it to
the Colloquium Mathematicum entry above, matching the site's /latex bibliography.)

Related OEIS sequences: none listed. Formalised statement in external databases:
No (as of the archived capture). The page records 1 comment (content not archived).

NOTE: the additions in this v2 file (module docstring only — the Lean statement is
unchanged from the input) are NOT compile-verified — the review container has no
Lean toolchain. The input `conjectures/1126.lean` is recorded as building
successfully in the original pipeline (session log e876e14a: "Build completed
successfully (2482 jobs)", sole warning the expected `sorry`).
-/

/--
Erdős Problem #1126 (posed in [Er60c]; proved independently by de Bruijn [dB66]
and Jurkat [Ju65]):

If f(x+y) = f(x) + f(y) for almost all x, y ∈ ℝ (planar Lebesgue measure) then
there exists a function g such that g(x+y) = g(x) + g(y) for all x, y ∈ ℝ and
f(x) = g(x) for almost all x.
-/
theorem erdos_problem_1126 (f : ℝ → ℝ)
    (hf : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), f (p.1 + p.2) = f p.1 + f p.2) :
    ∃ g : ℝ → ℝ,
      (∀ x y : ℝ, g (x + y) = g x + g y) ∧
      (∀ᵐ x ∂volume, f x = g x) :=
  sorry
