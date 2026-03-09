import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic

open scoped Classical
open Polynomial Complex Filter MeasureTheory ProbabilityTheory Finset

noncomputable section

/--
The number of roots (counted with multiplicity) of a polynomial over ℂ
that lie in the closed unit disk {z ∈ ℂ : ‖z‖ ≤ 1}.
-/
def rootsInUnitDisk (p : ℂ[X]) : ℕ :=
  (p.roots.filter (fun z => ‖z‖ ≤ 1)).card

/--
Erdős Problem #522 [Er61,p.252]:

Let f(z) = Σ_{k=0}^{n} ε_k z^k be a random polynomial, where ε_k ∈ {-1,1}
independently uniformly at random for 0 ≤ k ≤ n. Is it true that, if R_n is
the number of roots of f(z) in {z ∈ ℂ : |z| ≤ 1}, then R_n/(n/2) → 1
almost surely?

A weaker version (convergence in probability) was proved by Yakir (2021),
who showed P(|R_n - n/2| ≥ n^{9/10}) → 0.
-/
theorem erdos_problem_522
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℤ)
    (hε_meas : ∀ k, Measurable (ε k))
    (hε_val : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1)
    (hε_indep : iIndepFun ε P)
    (hε_unif : ∀ k, P {ω | ε k ω = 1} = 1 / 2) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n =>
        (rootsInUnitDisk
          (∑ k ∈ range (n + 1), C (↑(ε k ω) : ℂ) * X ^ k) : ℝ) / ((n : ℝ) / 2))
      atTop (nhds 1) :=
  sorry
