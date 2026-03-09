import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Filter Complex

noncomputable section

/-!
# Erdős Problem #513

Let f = ∑ aₙ zⁿ be a transcendental entire function. What is the greatest
possible value of

  lim inf_{r → ∞} max_n |aₙ rⁿ| / max_{|z|=r} |f(z)| ?

It is trivial that this value is in [1/2, 1). Kövári (unpublished) observed
that it must be > 1/2. Clunie and Hayman showed it is ≤ 2/π - c for some
absolute constant c > 0.

Reference: [Er61, p.249]
-/

/-- A power series f(z) = ∑ aₙ zⁿ is a transcendental entire function:
    the series converges everywhere on ℂ and infinitely many coefficients
    are nonzero (i.e., it is not a polynomial). -/
def IsTranscendentalEntire (a : ℕ → ℂ) : Prop :=
  (∀ z : ℂ, Summable (fun n => a n * z ^ n)) ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a n ≠ 0

/-- The maximum term μ(r) = max_n |aₙ| rⁿ for a power series with
    coefficients a and radius r ≥ 0. -/
noncomputable def maxTerm (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ n : ℕ, x = ‖a n‖ * r ^ n}

/-- The maximum modulus M(r) = max_{|z|=r} |f(z)| for a power series f
    with coefficients a. -/
noncomputable def maxModulus (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖∑' n, a n * z ^ n‖}

/-- The ratio μ(r)/M(r) for a given power series. -/
noncomputable def termModulusRatio (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  maxTerm a r / maxModulus a r

/--
Erdős Problem #513 [Er61, p.249]:

Determine the supremum, over all transcendental entire functions
f(z) = ∑ aₙ zⁿ, of lim inf_{r→∞} μ(r)/M(r), where μ(r) = max_n |aₙ rⁿ|
is the maximum term and M(r) = max_{|z|=r} |f(z)| is the maximum modulus.

This supremum is known to lie in (1/2, 2/π - c] for some c > 0, but the
exact value is unknown.
-/
theorem erdos_problem_513 :
    ∃ α : ℝ, 1 / 2 < α ∧ α < 1 ∧
      (∀ (a : ℕ → ℂ), IsTranscendentalEntire a →
        α ≤ Filter.liminf (fun r => termModulusRatio a r) atTop →
        False) ∧
      (∀ β : ℝ, β < α →
        ∃ (a : ℕ → ℂ), IsTranscendentalEntire a ∧
          β ≤ Filter.liminf (fun r => termModulusRatio a r) atTop) :=
  sorry

end
