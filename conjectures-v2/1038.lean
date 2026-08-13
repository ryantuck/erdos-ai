import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits

open Polynomial MeasureTheory Set

noncomputable section

/-!
# Erdős Problem #1038

Determine the infimum and supremum of |{x ∈ ℝ : |f(x)| < 1}| as f ∈ ℝ[x] ranges
over all non-constant monic polynomials, all of whose roots are real and in the
interval [-1,1].

A problem of Erdős, Herzog, and Piranian [EHP58, p.131]. Status on
erdosproblems.com/1038: OPEN (the infimum has not been determined; the supremum
is known). Page edition 11 January 2026.

Known results recorded on the problem page:
- [EHP58] proved the measure is at most 2√2 under the assumption that all roots
  are in {-1,1}, and conjectured this is the best possible upper bound. The
  supremum over the full class is now known: sup = 2√2 ≈ 2.828 (proof due to
  Tao [Tao25], per the upstream formal-conjectures file; the problem page
  attributes the current bounds to "the discussion in the comments").
- [EHP58] note the infimum is less than 2, witnessed by f(x) = (x+1)(x-1)^m
  for m ≥ 3.
- Current best known bounds for the infimum:
  1.519 ≈ 2^(4/3) - 1 ≤ inf ≤ 1.835...
- If the roots are instead restricted to [-2,2], the infimum is 0, witnessed by
  small perturbations of the Chebyshev polynomials. [EHP58] conjectured that,
  with roots restricted to [-2,2], the measure is ≥ n^(-c) for an absolute
  constant c > 0 (n the degree); this was proved by Pommerenke [Po61], who
  showed the set must in fact contain an interval of width ≫ n^(-4).

References:

[EHP58] Erdős, P., Herzog, F., and Piranian, G., _Metric properties of
polynomials_. J. Analyse Math. 6 (1958), 125-148.

[Po61] Pommerenke, Ch., _On metric properties of complex polynomials_.
Michigan Math. J. 8 (1961), 97-115.

[Tao25] Tao, T., _Sublevel Sets of Logarithmic Potentials_. Blog preprint,
December 2025. (Stub recovered from the upstream formal-conjectures file's
reference block; not cited on the erdosproblems.com page itself.)

The authoritative upstream formalization of this problem lives at
google-deepmind/formal-conjectures, file FormalConjectures/ErdosProblems/1038.lean.
-/

/--
The set of non-constant monic real polynomials that split over ℝ with all roots in [-1,1].
-/
def MonicRealRootsInUnitInterval : Set (Polynomial ℝ) :=
  { f : Polynomial ℝ |
    f.Monic ∧
    f.natDegree ≥ 1 ∧
    f.Splits ∧
    (∀ r : ℝ, f.IsRoot r → -1 ≤ r ∧ r ≤ 1) }

/--
The Lebesgue measure of the set {x ∈ ℝ : |f(x)| < 1} for a polynomial f.
-/
def sublevelMeasure (f : Polynomial ℝ) : ENNReal :=
  volume { x : ℝ | |f.eval x| < 1 }

/--
Erdős Problem #1038 [EHP58, p.131]:

Determine the infimum and supremum of |{x ∈ ℝ : |f(x)| < 1}| as f ranges over
all non-constant monic polynomials, all of whose roots are real and in [-1,1].

Erdős, Herzog, and Piranian proved that under the assumption all roots are in
{-1,1}, the measure is at most 2√2, and conjectured this is the best possible
upper bound. The supremum is now known to equal 2√2 [Tao25].

This theorem records the solved supremum half of the problem. (Note the
supremum is attained: f(x) = x² - 1 has sublevel set (-√2, √2) \ {0}, of
measure exactly 2√2.)
-/
theorem erdos_problem_1038_sup :
    ⨆ f ∈ MonicRealRootsInUnitInterval, sublevelMeasure f =
      ENNReal.ofReal (2 * Real.sqrt 2) :=
  sorry

/--
Erdős Problem #1038 (infimum, lower bound): the infimum of |{x ∈ ℝ : |f(x)| < 1}|
over all non-constant monic polynomials with all roots real and in [-1,1] is at
least 2^(4/3) - 1 ≈ 1.519. This is the best known lower bound per
erdosproblems.com/1038 (attributed there to the discussion in the comments);
the exact value of the infimum is OPEN.
-/
theorem erdos_problem_1038_inf_lower :
    ENNReal.ofReal (2 ^ (4 / 3 : ℝ) - 1) ≤
      ⨅ f ∈ MonicRealRootsInUnitInterval, sublevelMeasure f :=
  sorry

/--
Erdős Problem #1038 (infimum, upper bound): the infimum is at most 1.835...
(erdosproblems.com/1038, from the discussion in the comments). The page states
the bound as the truncated decimal "1.835⋯" of an unspecified constant in
[1.835, 1.836), so the literal claim safely derivable from it is inf < 1.836,
formalized here. (The upstream formal-conjectures file states inf < 1.835,
which does not follow from the page's "inf ≤ 1.835⋯" if the constant exceeds
1.835.)
-/
theorem erdos_problem_1038_inf_upper :
    ⨅ f ∈ MonicRealRootsInUnitInterval, sublevelMeasure f <
      ENNReal.ofReal 1.836 :=
  sorry

/--
Erdős, Herzog, and Piranian [EHP58] noted that the infimum is less than 2,
witnessed by f(x) = (x+1)(x-1)^m for m ≥ 3. (Subsumed by
`erdos_problem_1038_inf_upper`, but recorded separately as it is the bound
with a citable source.)
-/
theorem erdos_problem_1038_inf_lt_two :
    ⨅ f ∈ MonicRealRootsInUnitInterval, sublevelMeasure f < 2 :=
  sorry

/--
The infimum is strictly positive. This is a weak consequence of
`erdos_problem_1038_inf_lower`; retained from the original formalization.
-/
theorem erdos_problem_1038_inf :
    ⨅ f ∈ MonicRealRootsInUnitInterval, sublevelMeasure f > 0 :=
  sorry

/--
Erdős, Herzog, and Piranian [EHP58] proved that if all roots of a non-constant
monic real polynomial lie in {-1,1}, then |{x ∈ ℝ : |f(x)| < 1}| ≤ 2√2.
-/
theorem erdos_problem_1038_roots_pm_one_le :
    ∀ f : Polynomial ℝ, f.Monic → f.natDegree ≥ 1 → f.Splits →
      (∀ r : ℝ, f.IsRoot r → r = -1 ∨ r = 1) →
      sublevelMeasure f ≤ ENNReal.ofReal (2 * Real.sqrt 2) :=
  sorry

/--
If the roots are instead restricted to [-2,2], the infimum of
|{x ∈ ℝ : |f(x)| < 1}| is zero, witnessed by small perturbations of the
Chebyshev polynomials [EHP58].
-/
theorem erdos_problem_1038_interval_two_inf_zero :
    ⨅ f ∈ { f : Polynomial ℝ |
        f.Monic ∧ f.natDegree ≥ 1 ∧ f.Splits ∧
        (∀ r : ℝ, f.IsRoot r → -2 ≤ r ∧ r ≤ 2) },
      sublevelMeasure f = 0 :=
  sorry

/--
Pommerenke [Po61] proved the Erdős–Herzog–Piranian conjecture that, for
non-constant monic real polynomials of degree n with all roots real and in
[-2,2], the measure |{x ∈ ℝ : |f(x)| < 1}| is at least n^(-c) for an absolute
constant c > 0. (He showed more: the set contains an interval of width
≫ n^(-4).)
-/
theorem erdos_problem_1038_pommerenke :
    ∃ c : ℝ, c > 0 ∧ ∀ f : Polynomial ℝ,
      f.Monic → f.natDegree ≥ 1 → f.Splits →
      (∀ r : ℝ, f.IsRoot r → -2 ≤ r ∧ r ≤ 2) →
      ENNReal.ofReal ((f.natDegree : ℝ) ^ (-c)) ≤ sublevelMeasure f :=
  sorry

end
