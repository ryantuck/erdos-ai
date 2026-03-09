import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth

open Nat

noncomputable section

/-- The k-th primorial: product of the first k primes.
    primorial 0 = 1, primorial 1 = 2, primorial 2 = 6, primorial 3 = 30. -/
noncomputable def primorial779 : ℕ → ℕ
  | 0 => 1
  | k + 1 => Nat.nth Nat.Prime k * primorial779 k

/--
Erdős Problem #779 [Gu83]:

Let n > 1 and let p₁ < p₂ < ⋯ < pₙ denote the first n primes.
Let P = p₁ · p₂ · ⋯ · pₙ (the n-th primorial).
Does there always exist some prime p with pₙ < p < P such that P + p is prime?

A problem of Deaconescu. Deaconescu has verified this for n ≤ 1000.
-/
theorem erdos_problem_779 :
    ∀ n : ℕ, n > 1 →
      ∃ p : ℕ, Nat.Prime p ∧
        Nat.nth Nat.Prime (n - 1) < p ∧
        p < primorial779 n ∧
        Nat.Prime (primorial779 n + p) :=
  sorry

end
