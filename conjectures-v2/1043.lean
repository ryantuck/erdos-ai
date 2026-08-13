import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Polynomial MeasureTheory Complex

noncomputable section

/-- The sublevel set (lemniscate) of a polynomial f: {z ∈ ℂ : ‖f(z)‖ ≤ 1}. -/
def sublevelSet1043 (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

/-- Projection of a subset of ℂ onto the line through the origin at angle θ:
    the set {Re(z) · cos θ + Im(z) · sin θ | z ∈ S}. -/
def lineProjection1043 (S : Set ℂ) (θ : ℝ) : Set ℝ :=
  {t : ℝ | ∃ z ∈ S, t = z.re * Real.cos θ + z.im * Real.sin θ}

/--
Erdős Problem #1043 [EHP58]:

Let f ∈ ℂ[x] be a monic non-constant polynomial. Must there exist a straight
line ℓ such that the projection of {z : |f(z)| ≤ 1} onto ℓ has measure at
most 2?

A problem of Erdős, Herzog, and Piranian. The answer is NO: disproved by
Pommerenke [Po61] (using [Po59]), who showed there exists a monic polynomial
f for which the projection of {z : |f(z)| ≤ 1} onto every line has measure
at least 2.386. On the other hand, Pommerenke also proved there always
exists a line such that the projection has measure at most 3.3.

The statement below is accordingly the NEGATION of the question's universal
form, i.e. the true (refuting) direction. Status on erdosproblems.com:
DISPROVED (LEAN) — "solved in the negative and the proof verified in Lean"
(page last edited 06 January 2026, snapshot accessed 2026-03-06; tag:
analysis). The upstream formalization in google-deepmind/formal-conjectures
(FormalConjectures/ErdosProblems/1043.lean) encodes this as
`answer(False) ↔ (∀ f, …)`, equivalent to the negation asserted here; the
Lean proof of the refutation is due to Alexeev using Aristotle
(github.com/plby/lean-proofs, src/v4.24.0/ErdosProblems/Erdos1043.lean).

References:
- [EHP58] Erdős, P., Herzog, F., and Piranian, G., Metric properties of
  polynomials. J. Analyse Math. 6 (1958), 125-148.
- [Po59] Pommerenke, Ch., On some problems by Erdős, Herzog and Piranian.
  Michigan Math. J. 6 (1959), 221-225.
- [Po61] Pommerenke, Ch., On metric properties of complex polynomials.
  Michigan Math. J. 8 (1961), 97-115.
-/
theorem erdos_problem_1043 :
    ¬ (∀ (f : Polynomial ℂ), f.Monic → 1 ≤ f.natDegree →
      ∃ θ : ℝ,
        volume (lineProjection1043 (sublevelSet1043 f) θ) ≤ ENNReal.ofReal 2) :=
  sorry

/--
Erdős Problem #1043, lower-bound variant [Po61]:

Pommerenke's refutation in quantitative form: there exists a monic
non-constant polynomial f such that the projection of {z : |f(z)| ≤ 1} onto
EVERY line has measure at least 2.386. This implies `erdos_problem_1043`
(confirmed by the erdosproblems.com remarks, snapshot accessed 2026-03-06).
-/
theorem erdos_problem_1043.variants.pommerenke_lower :
    ∃ f : Polynomial ℂ, f.Monic ∧ 1 ≤ f.natDegree ∧
      ∀ θ : ℝ,
        ENNReal.ofReal 2.386 ≤ volume (lineProjection1043 (sublevelSet1043 f) θ) :=
  sorry

/--
Erdős Problem #1043, upper-bound variant [Po61]:

In the positive direction, Pommerenke proved that for every monic
non-constant polynomial f there always exists a line such that the
projection of {z : |f(z)| ≤ 1} onto it has measure at most 3.3 (confirmed
by the erdosproblems.com remarks, snapshot accessed 2026-03-06).
-/
theorem erdos_problem_1043.variants.pommerenke_upper :
    ∀ (f : Polynomial ℂ), f.Monic → 1 ≤ f.natDegree →
      ∃ θ : ℝ,
        volume (lineProjection1043 (sublevelSet1043 f) θ) ≤ ENNReal.ofReal 3.3 :=
  sorry

end
