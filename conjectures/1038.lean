import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped Real ENNReal
open MeasureTheory Polynomial Classical

noncomputable section

/-!
# Erdős Problem #1038

Determine the infimum and supremum of |{x ∈ ℝ : |f(x)| < 1}| as f ranges
over all non-constant monic polynomials, all of whose roots are real and in
the interval [-1, 1].

A problem of Erdős, Herzog, and Piranian [EHP58, p.131].

Known bounds:
- 2^{4/3} - 1 ≤ inf ≤ 1.835...
- sup = 2√2

The supremum 2√2 was proved by Tao [Tao25].
-/

/--
Erdős Problem #1038 (infimum, lower bound):

The infimum of the Lebesgue measure of {x ∈ ℝ : |f(x)| < 1} over all
non-constant monic polynomials with all roots real and in [-1, 1] is at
least 2^{4/3} - 1 ≈ 1.519.
-/
theorem erdos_problem_1038_inf_lower :
    ENNReal.ofReal (2 ^ (4 / 3 : ℝ) - 1) ≤
    ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
      (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x : ℝ | |f.1.eval x| < 1} :=
  sorry

/--
Erdős Problem #1038 (infimum, upper bound):

The infimum is less than 1.835, as witnessed by f(x) = (x+1)(x-1)^m for
large m.
-/
theorem erdos_problem_1038_inf_upper :
    ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
      (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x : ℝ | |f.1.eval x| < 1} <
    ENNReal.ofReal 1.835 :=
  sorry

/--
Erdős Problem #1038 (supremum):

The supremum of the Lebesgue measure of {x ∈ ℝ : |f(x)| < 1} over all
monic polynomials with all roots real and in [-1, 1] equals 2√2.

Proved by Tao [Tao25].
-/
theorem erdos_problem_1038_sup :
    ⨆ f : {f : Polynomial ℝ // f.Monic ∧
      (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x : ℝ | |f.1.eval x| < 1} =
    ENNReal.ofReal (2 * Real.sqrt 2) :=
  sorry

end
