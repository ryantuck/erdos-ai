import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic

open Classical Finset Real

noncomputable section

/-- A natural number `n` is highly composite if every smaller positive natural
    number has strictly fewer divisors. -/
def IsHighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → (Nat.divisors m).card < (Nat.divisors n).card

/-- `highlyCompositeCount x` counts the number of highly composite numbers in `[1, x]`. -/
noncomputable def highlyCompositeCount (x : ℕ) : ℕ :=
  ((Finset.range x).filter (fun n => IsHighlyComposite (n + 1))).card

/--
Erdős Problem #381 (Disproved) [Er44]:

A number n is highly composite if τ(m) < τ(n) for all m < n, where τ(m)
counts the number of divisors of m. Let Q(x) count the number of highly
composite numbers in [1, x].

Erdős asked whether Q(x) ≫_k (log x)^k for every k ≥ 1.

Erdős [Er44] proved Q(x) ≫ (log x)^{1+c} for some constant c > 0.

The answer is no: Nicolas [Ni71] proved that Q(x) ≪ (log x)^{O(1)},
i.e., there exist constants C and K such that Q(x) ≤ C · (log x)^K
for all sufficiently large x.

We formalize Nicolas's result, which is the true (negative) answer.
-/
theorem erdos_problem_381 :
    ∃ (C K : ℝ), 0 < C ∧ 0 < K ∧
      ∃ N₀ : ℕ, ∀ x : ℕ, N₀ ≤ x →
        (highlyCompositeCount x : ℝ) ≤ C * (Real.log (x : ℝ)) ^ K :=
  sorry

end
