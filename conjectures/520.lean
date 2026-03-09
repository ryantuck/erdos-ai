import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.LiminfLimsup

open MeasureTheory BigOperators Finset Real Filter

noncomputable section

/--
A function f : ℕ → ℤ is a Rademacher multiplicative function if:
- f(1) = 1
- f(p) ∈ {-1, 1} for each prime p
- f(n) = ∏_{p | n} f(p) when n is squarefree and positive
- f(n) = 0 when n is not squarefree (and n > 0)
-/
def IsRademacherMultiplicative (f : ℕ → ℤ) : Prop :=
  f 1 = 1 ∧
  (∀ p, Nat.Prime p → f p = 1 ∨ f p = -1) ∧
  (∀ n, 0 < n → Squarefree n → f n = ∏ p ∈ n.primeFactors, f p) ∧
  (∀ n, 0 < n → ¬Squarefree n → f n = 0)

/--
Erdős Problem #520 [Er61, p.251]:

Let f be a Rademacher multiplicative function: for each prime p, independently
choose f(p) ∈ {-1, 1} uniformly at random, extend multiplicatively to squarefree
integers (f(n) = 0 if n is not squarefree). Does there exist a constant c > 0
such that, almost surely,
  limsup_{N → ∞} (∑_{m ≤ N} f(m)) / √(N log log N) = c?

This is analogous to the law of the iterated logarithm for independent random
variables (where c = √2), but here the multiplicative structure constrains f.
-/
theorem erdos_problem_520
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℕ → ℤ)
    (hf : ∀ᵐ ω ∂μ, IsRademacherMultiplicative (f ω))
    (hind : ∀ p, Nat.Prime p → μ {ω | f ω p = 1} = 1 / 2) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᵐ ω ∂μ,
        Filter.limsup (fun N =>
          (∑ m ∈ Finset.Icc 1 N, (f ω m : ℝ)) /
          Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ)))) Filter.atTop = c :=
  sorry

end
