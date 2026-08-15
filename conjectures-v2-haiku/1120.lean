import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.EMetricSpace.BoundedVariation

noncomputable section
open Complex Polynomial Set

namespace Erdos1120

/-- The lemniscate (sublevel) set of a polynomial f: {z ∈ ℂ : ‖f(z)‖ ≤ 1}. -/
def lemniscateSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

/--
Erdős Problem #1120 [Ha74, Problem 4.22]:

Let f ∈ ℂ[z] be a monic polynomial of degree n, all of whose roots satisfy |z| ≤ 1.
Let E = {z : |f(z)| ≤ 1}. The worst-case shortest length of a path in E joining
z = 0 to |z| = 1 tends to infinity with n.

Erdős wrote "presumably this tends to infinity with n, but not too fast."
The trivial lower bound is 1 (achieved by f(z) = z^n). Clunie and Netanyahu
showed that a path always exists joining z = 0 to |z| = 1 in E.

Formally: for every C > 0, there exists N such that for all n ≥ N, there exists a
monic polynomial f of degree n with all roots in the closed unit disk, such that
every continuous path γ : [0,1] → E from 0 to the unit circle has arc length ≥ C.
-/
theorem erdos_problem_1120 :
    ∀ C : ℝ, C > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ f : Polynomial ℂ, f.Monic ∧ f.natDegree = n ∧
      (∀ z ∈ f.roots, ‖z‖ ≤ 1) ∧
      ∀ γ : ℝ → ℂ, Continuous γ →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ lemniscateSet f) →
        γ 0 = 0 →
        ‖γ 1‖ = 1 →
        ENNReal.ofReal C ≤ eVariationOn γ (Icc (0 : ℝ) 1) :=
  sorry

end Erdos1120
