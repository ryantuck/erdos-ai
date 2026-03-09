import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic

open Nat Set

noncomputable section

/--
For a natural number `a` in the range of Euler's totient function,
`minTotientPreimage a h` is the smallest `n` such that `φ(n) = a`.
-/
def minTotientPreimage (a : ℕ) (h : ∃ n, Nat.totient n = a) : ℕ :=
  Nat.find h

/--
Erdős Problem #51 [Er95, Er98]:

Is there an infinite set A ⊂ ℕ such that for every a ∈ A there is an integer n
with φ(n) = a, and yet if n_a is the smallest such integer then n_a / a → ∞
as a → ∞ (within A)?
-/
theorem erdos_problem_51 :
    ∃ A : Set ℕ, A.Infinite ∧
      (∀ a ∈ A, ∃ n, Nat.totient n = a) ∧
      ∀ C : ℝ, 0 < C →
        ∃ N : ℕ, ∀ a ∈ A, a ≥ N →
          ∀ (h : ∃ n, Nat.totient n = a),
            (↑(minTotientPreimage a h) : ℝ) / (↑a : ℝ) ≥ C :=
  sorry
