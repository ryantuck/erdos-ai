import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real

noncomputable section

/--
Erdős Problem #238 [Er55c]:

Let c₁, c₂ > 0. Is it true that, for any sufficiently large x, there exist
more than c₁ log x many consecutive primes ≤ x such that the difference
between any two is > c₂?

Here "consecutive primes" means a block p_{m}, p_{m+1}, …, p_{m+k} of
consecutively indexed primes. The conjecture asks for such a block of length
> c₁ log x where every pairwise difference exceeds c₂.

Erdős [Er49c] proved this is true for any c₂ > 0 if c₁ > 0 is sufficiently
small (depending on c₂).
-/
theorem erdos_problem_238 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        ∃ m k : ℕ, c₁ * Real.log (x : ℝ) < (k : ℝ) ∧
          (∀ i, i ≤ k → nth Nat.Prime (m + i) ≤ x) ∧
          (∀ i j, i ≤ k → j ≤ k → i ≠ j →
            c₂ < |((nth Nat.Prime (m + i) : ℤ) - (nth Nat.Prime (m + j) : ℤ))| ) :=
  sorry

end
