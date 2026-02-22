import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

open Complex Polynomial Metric Set

noncomputable section

/-!
# Erdős Problem #1048

If f ∈ ℂ[x] is a monic polynomial with all roots satisfying |z| ≤ r for some
r < 2, must { z : |f(z)| < 1 } have a connected component with diameter > 2 − r?

A problem of Erdős, Herzog, and Piranian [EHP58,p.142].

Pommerenke [Po61] proved the answer is no for r > 1, showing that if
f(z) = zⁿ − rⁿ then { z : |f(z)| ≤ 1 } has n connected components, all with
diameter → 0 as n → ∞.

For 0 < r ≤ 1, the answer is yes (also Pommerenke [Po61]).
-/

/--
Erdős Problem #1048 [EHP58,p.142] (disproved by Pommerenke [Po61]):

There exists r < 2 and a monic polynomial f ∈ ℂ[x] with all roots in the closed
disk of radius r such that every connected component of { z : ‖f(z)‖ < 1 } has
diameter at most 2 − r.
-/
theorem erdos_problem_1048 :
    ∃ (r : ℝ), r < 2 ∧
    ∃ (f : Polynomial ℂ), f.Monic ∧
      (∀ z ∈ f.roots, ‖z‖ ≤ r) ∧
      let S := {z : ℂ | ‖Polynomial.eval z f‖ < 1}
      ∀ z ∈ S, Metric.diam (connectedComponentIn S z) ≤ 2 - r :=
  sorry

end
