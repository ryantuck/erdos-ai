import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Complex Finset BigOperators

noncomputable section

/-!
# Erdős Problem #1045

Let z_1, ..., z_n ∈ ℂ with |z_i - z_j| ≤ 2 for all i,j, and
  Δ(z_1,...,z_n) = ∏_{i≠j} |z_i - z_j|.

What is the maximum possible value of Δ? Is it maximised by taking the z_i
to be the vertices of a regular polygon inscribed in a circle of diameter 2?

A problem of Erdős, Herzog, and Piranian [EHP58]. Hu and Tang found
counterexamples for n = 4 and n = 6. Cambie showed that the regular polygon
does not maximise Δ for any even n ≥ 4. The question remains open for odd n.
-/

/-- The product Δ(z) = ∏_{i ≠ j} ‖z i - z j‖ for a configuration z : Fin n → ℂ. -/
noncomputable def erdosDelta (n : ℕ) (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i ≠ j then ‖z i - z j‖ else 1

/-- The vertices of a regular n-gon inscribed in the unit circle (diameter 2). -/
noncomputable def regularNGon (n : ℕ) : Fin n → ℂ :=
  fun k => exp (ofReal (2 * Real.pi * (k.val : ℝ) / (n : ℝ)) * I)

/--
Erdős Problem #1045 [EHP58,p.143]:

For all n ≥ 1 and all z_1,...,z_n ∈ ℂ with |z_i - z_j| ≤ 2,
the product Δ(z_1,...,z_n) = ∏_{i≠j} |z_i - z_j| is maximised when the z_i
are the vertices of a regular n-gon inscribed in a circle of diameter 2.

Note: This has been disproved for all even n ≥ 4 (Hu-Tang, Cambie).
The conjecture remains open for odd n.
-/
theorem erdos_problem_1045 (n : ℕ) (hn : n ≥ 1) (z : Fin n → ℂ)
    (hd : ∀ i j : Fin n, ‖z i - z j‖ ≤ 2) :
    erdosDelta n z ≤ erdosDelta n (regularNGon n) :=
  sorry

end
