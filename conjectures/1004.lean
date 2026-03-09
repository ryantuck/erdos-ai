import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Real

/--
Erdős Problem #1004 [Er85e]:

Let c > 0. If x is sufficiently large then does there exist n ≤ x such that the
values of φ(n+k) are all distinct for 1 ≤ k ≤ (log x)^c, where φ is the Euler
totient function?

See [945] for the analogous problem with the divisor function.
-/
theorem erdos_problem_1004 :
    ∀ c : ℝ, 0 < c →
      ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ →
        ∃ n : ℕ, n ≤ x ∧
          ∀ j k : ℕ, 1 ≤ j → j ≤ ⌊(Real.log (x : ℝ)) ^ c⌋₊ →
            1 ≤ k → k ≤ ⌊(Real.log (x : ℝ)) ^ c⌋₊ →
            j ≠ k → Nat.totient (n + j) ≠ Nat.totient (n + k) :=
  sorry
