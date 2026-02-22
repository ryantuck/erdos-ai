import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod

open Finset

noncomputable section

/--
Erdős Problem #884 [Er98]:
Is it true that, for any n, if d₁ < ⋯ < dₜ are the divisors of n, then
  ∑_{1 ≤ i < j ≤ t} 1/(dⱼ - dᵢ) ≪ 1 + ∑_{1 ≤ i < t} 1/(d_{i+1} - dᵢ),
where the implied constant is absolute?

The double sum over all pairs of divisors is bounded (up to an absolute constant)
by 1 plus the sum over consecutive divisor gaps. Two divisors are consecutive
if no other divisor of n lies strictly between them.

See also problem #144.
-/
theorem erdos_problem_884 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (∑ p ∈ (n.divisors ×ˢ n.divisors).filter (fun p => p.1 < p.2),
        (1 : ℝ) / ((p.2 : ℝ) - (p.1 : ℝ))) ≤
      C * (1 + ∑ p ∈ (n.divisors ×ˢ n.divisors).filter (fun p =>
        p.1 < p.2 ∧ ∀ e ∈ n.divisors, ¬(p.1 < e ∧ e < p.2)),
        (1 : ℝ) / ((p.2 : ℝ) - (p.1 : ℝ))) :=
  sorry

end
