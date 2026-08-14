import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Real.Basic
-- Import added in v2 for the `Measurable` hypothesis of the Kemperman variant below.
-- It provides `Real.measurableSpace` (verified present in this module at the repo's
-- pinned Mathlib rev 8f9d9cf, v4.28.0, line 698) — NOT compile-verified in this container.
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Erdős Problem #1125

Source: https://www.erdosproblems.com/1125 (full archived HTML capture, accessed
2026-02-23, recovered from the session logs; two copies inside that capture and a
structured re-capture in the upstream formal-conjectures logs agree on every field).
Page edition: 30 December 2025.

Verbatim statement: "Let $f:\mathbb{R}\to \mathbb{R}$ be such that
\[2f(x) \leq f(x+h)+f(x+2h)\]
for every $x\in \mathbb{R}$ and $h>0$. Must $f$ be monotonic?"

Status: PROVED (banner tooltip: "This has been solved in the affirmative.").
Problem source: [Er81b, p.31]. Tag: analysis.

Remarks from the page (verbatim): "A problem of Kemperman [Ke69], who proved it is
true if $f$ is measurable. Erdős [Er81b] wrote 'if it were my problem I would offer
\$500 for it'. This was solved by Laczkovich [La84]."

Encoding notes.

1. The source poses a yes/no question ("Must $f$ be monotonic?"). This raw-file
   corpus has no `answer()` elaborator, so the theorem directly asserts the
   affirmative answer — the true direction, per Laczkovich [La84].
2. "Monotonic" is encoded as `Monotone f ∨ Antitone f` (non-decreasing or
   non-increasing), the standard two-sided reading. Under the hypothesis the
   `Antitone` disjunct collapses: if $f$ is antitone then for $h > 0$ both
   $f(x+h) \le f(x)$ and $f(x+2h) \le f(x)$, so the hypothesis forces
   $f(x+h) = f(x)$ for all $x$ and $h > 0$, i.e. $f$ is constant (hence also
   `Monotone`). The disjunction is therefore equivalent, under the hypothesis, to
   the sharp form `Monotone f` actually proved by Laczkovich; the disjunctive form
   is kept as the faithful rendering of "monotonic" as asked.
3. Kemperman's partial result (measurable case), stated verbatim on the page, is
   formalized below as `erdos_problem_1125.variants.measurable`.

References (keys as on the recovered page; bibliographic data recovered from the
archived WebFetch of erdosproblems.com/latex/1125 in the upstream session logs —
volume numbers were absent from that extraction and are NOT supplied here):

[Ke69] Kemperman, J. H. B., _On the regularity of generalized convex functions_.
Trans. Amer. Math. Soc. (1969), 69-93.

[Er81b] Erdős, P., _My Scottish Book 'Problems'_. The Scottish Book (1981), 27-35
(2nd edition).

[La84] Laczkovich, M., _On Kemperman's inequality 2f(x)≤f(x+h)+f(x+2h)_.
Colloq. Math. (1984), 109-115.

Related OEIS sequences: none listed. Formalised statement in external databases:
No (as of the archived capture). The page records 0 comments.

NOTE: the additions in this v2 file (module docstring, [Er81b, p.31] page
reference, measurable variant and its import) are NOT compile-verified — the
review container has no Lean toolchain. The input `conjectures/1125.lean` is
recorded as building successfully in the original pipeline (session log 6681e018:
"Build completed successfully (759 jobs)", sole warning the expected `sorry`).
-/

/--
Erdős Problem #1125 (Proved by Laczkovich [La84]):
Let f : ℝ → ℝ be such that 2f(x) ≤ f(x+h) + f(x+2h) for every x ∈ ℝ and h > 0.
Must f be monotonic?

A problem of Kemperman [Ke69], who proved it is true if f is measurable
(see `erdos_problem_1125.variants.measurable`). The problem appears in
Erdős [Er81b, p.31], who wrote "if it were my problem I would offer $500 for it".
Laczkovich [La84] solved it in the affirmative.
-/
theorem erdos_problem_1125 :
    ∀ f : ℝ → ℝ,
    (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    Monotone f ∨ Antitone f :=
  sorry

/--
Erdős Problem #1125, measurable variant — Kemperman's partial result [Ke69],
page-confirmed ("A problem of Kemperman [Ke69], who proved it is true if $f$ is
measurable"):

If f : ℝ → ℝ is measurable and 2f(x) ≤ f(x+h) + f(x+2h) for every x ∈ ℝ and
h > 0, then f is monotonic. This is the special case of `erdos_problem_1125`
under the additional measurability hypothesis, proved by Kemperman fifteen years
before Laczkovich removed the hypothesis.

NOTE: added from the recovered source page; not compile-verified (requires the
`Mathlib.MeasureTheory.Constructions.BorelSpace.Basic` import added above).
-/
theorem erdos_problem_1125.variants.measurable :
    ∀ f : ℝ → ℝ, Measurable f →
    (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    Monotone f ∨ Antitone f :=
  sorry
