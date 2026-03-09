import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Real.Basic

open Classical Finset

/--
Erdős Problem #851 [Er85c]:

Let ε > 0. Is there some r (depending on ε) such that the density of integers
of the form 2^k + n, where k ≥ 0 and n has at most r prime divisors, is at
least 1 - ε?

This was proved by Romanoff [Ro34] for the weaker statement that {2^k + p : p prime}
has positive lower density. See also problem [205].
-/
theorem erdos_problem_851 :
    ∀ ε : ℝ, ε > 0 →
      ∃ r : ℕ,
        ∀ δ : ℝ, δ > 0 →
          ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
            (((Finset.range N).filter (fun m =>
              ∃ k : ℕ, ∃ n : ℕ, m = 2 ^ k + n ∧
                n.primeFactors.card ≤ r)).card : ℝ) / (N : ℝ) > 1 - ε - δ :=
  sorry
