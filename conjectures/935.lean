import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Real

noncomputable section

/-!
# Erdős Problem #935

For any integer n = ∏ p^{k_p} let Q₂(n) be the powerful part of n, so that
Q₂(n) = ∏_{p, k_p ≥ 2} p^{k_p}.

1. Is it true that, for every ε > 0 and ℓ ≥ 1, if n is sufficiently large then
   Q₂(n(n+1)⋯(n+ℓ)) < n^{2+ε}?

2. If ℓ ≥ 2 then is limsup_{n → ∞} Q₂(n(n+1)⋯(n+ℓ))/n² infinite?

3. If ℓ ≥ 2 then is lim_{n → ∞} Q₂(n(n+1)⋯(n+ℓ))/n^{ℓ+1} = 0?

The second part is resolved affirmatively: a construction via solutions to the
Pell equation x² - 8y² = 1 shows limsup Q₂(n(n+1)(n+2))/n² = ∞.
-/

/-- The powerful (2-full) part of a natural number n: the product of all prime
    power factors p^a where a ≥ 2. -/
def powerfulPart (n : ℕ) : ℕ :=
  (n.factorization.support.filter (fun p => 2 ≤ n.factorization p)).prod
    (fun p => p ^ n.factorization p)

/--
Erdős Problem #935, Part 1:

For every ε > 0 and ℓ ≥ 1, if n is sufficiently large then
  Q₂(n(n+1)⋯(n+ℓ)) < n^{2+ε}.
-/
theorem erdos_problem_935_part1 :
    ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (powerfulPart (∏ i ∈ Finset.range (ℓ + 1), (n + i)) : ℝ) <
        (n : ℝ) ^ ((2 : ℝ) + ε) :=
  sorry

/--
Erdős Problem #935, Part 2 (resolved):

For every ℓ ≥ 2, limsup_{n → ∞} Q₂(n(n+1)⋯(n+ℓ))/n² = ∞.
This was proved via solutions to the Pell equation x² - 8y² = 1.
Formulated as: for every M and N, there exists n ≥ N such that
  Q₂(n(n+1)⋯(n+ℓ)) > M · n².
-/
theorem erdos_problem_935_part2 :
    ∀ ℓ : ℕ, 2 ≤ ℓ →
    ∀ M : ℝ, ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧
      (powerfulPart (∏ i ∈ Finset.range (ℓ + 1), (n + i)) : ℝ) >
        M * ((n : ℝ) ^ (2 : ℕ)) :=
  sorry

/--
Erdős Problem #935, Part 3:

For every ℓ ≥ 2, lim_{n → ∞} Q₂(n(n+1)⋯(n+ℓ))/n^{ℓ+1} = 0.
Formulated as: for every ε > 0, Q₂(n(n+1)⋯(n+ℓ)) < ε · n^{ℓ+1} for all
sufficiently large n.
-/
theorem erdos_problem_935_part3 :
    ∀ ℓ : ℕ, 2 ≤ ℓ →
    ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (powerfulPart (∏ i ∈ Finset.range (ℓ + 1), (n + i)) : ℝ) <
        ε * ((n : ℝ) ^ ((ℓ : ℝ) + 1)) :=
  sorry

end
